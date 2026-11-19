package main

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"net/url"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"time"

	fhttp "github.com/bogdanfinn/fhttp"
	tlsclient "github.com/bogdanfinn/tls-client"
	"github.com/bogdanfinn/tls-client/profiles"
)

type Address struct {
	Address1    string
	City        string
	PostalCode  string
	ZoneCode    string
	CountryCode string
	Phone       string
}

var addressBook = map[string][]Address{
	"US": {
		{"350 Fifth Ave", "New York", "10118", "NY", "US", "2125550100"},
		{"233 S Wacker Dr", "Chicago", "60606", "IL", "US", "3125550147"},
		{"1 Apple Park Way", "Cupertino", "95014", "CA", "US", "4085550100"},
		{"888 Brickell Ave", "Miami", "33131", "FL", "US", "3055550189"},
	},
}

var defaultAddresses = []Address{
	{"350 Fifth Ave", "New York", "10118", "NY", "US", "2125550100"},
}

var currencyToCountry = map[string]string{
	"USD": "US", "GBP": "GB", "CAD": "CA",
}

type UAProfile struct {
	UA         string
	ChUA       string
	ChMobile   string
	ChPlatform string
}

var uaProfiles = []UAProfile{
	{"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36", `"Chromium";v="124", "Google Chrome";v="124", "Not-A.Brand";v="99"`, "?0", `"Windows"`},
}

var (
	firstNames   = []string{"James", "John", "Robert", "Michael", "William"}
	lastNames    = []string{"Smith", "Johnson", "Williams", "Brown", "Jones"}
	emailDomains = []string{"gmail.com", "yahoo.com", "outlook.com"}
	acceptLangs  = []string{"en-US,en;q=0.9"}
)

var apiStartTime = time.Now()

var (
	binCache     sync.Map
	pciSemaphore = make(chan struct{}, 200)
	tlsProfiles  = []profiles.ClientProfile{
		profiles.Chrome_120,
		profiles.Chrome_124,
	}
)

const (
	tgBotToken   = ""
	maxWorkers   = 600
	batchWorkers = 400
	maxRetries   = 5
)

var tgChatIDs = []string{}

type BINInfo struct {
	Brand   string
	Type    string
	Level   string
	Bank    string
	Country string
	Flag    string
}

var binFallback = BINInfo{"-", "-", "-", "-", "-", ""}

type ProductResult struct {
	Site             string
	Price            string
	VariantID        string
	RequiresShipping bool
}

type CheckResult struct {
	Success  bool
	Response string
	Gateway  string
	Price    string
	Currency string
}

func pickUAProfile() UAProfile {
	return uaProfiles[rand.Intn(len(uaProfiles))]
}

func pickAddr(rawURL string) Address {
	u, err := url.Parse(rawURL)
	tld := ""
	if err == nil {
		parts := strings.Split(u.Hostname(), ".")
		if len(parts) > 0 {
			tld = strings.ToUpper(parts[len(parts)-1])
		}
	}
	if addrs, ok := addressBook[tld]; ok {
		return addrs[rand.Intn(len(addrs))]
	}
	return defaultAddresses[rand.Intn(len(defaultAddresses))]
}

func pickAddrByCountry(cc string) Address {
	if addrs, ok := addressBook[strings.ToUpper(cc)]; ok {
		return addrs[rand.Intn(len(addrs))]
	}
	return defaultAddresses[rand.Intn(len(defaultAddresses))]
}

func randomName() (string, string) {
	return firstNames[rand.Intn(len(firstNames))], lastNames[rand.Intn(len(lastNames))]
}

func generateEmail(first, last string) string {
	n := rand.Intn(999) + 1
	variants := []string{
		strings.ToLower(first) + "." + strings.ToLower(last),
		strings.ToLower(first) + strings.ToLower(last) + strconv.Itoa(n),
	}
	return variants[rand.Intn(len(variants))] + "@" + emailDomains[rand.Intn(len(emailDomains))]
}

func buildProxyURL(proxyStr string) string {
	if proxyStr == "" {
		return ""
	}
	s := strings.TrimSpace(proxyStr)
	if strings.HasPrefix(s, "http://") || strings.HasPrefix(s, "https://") || strings.HasPrefix(s, "socks") {
		return s
	}
	parts := strings.Split(s, ":")
	switch len(parts) {
	case 2:
		return "http://" + s
	case 4:
		return fmt.Sprintf("http://%s:%s@%s:%s", parts[2], parts[3], parts[0], parts[1])
	case 3:
		return "http://" + s
	}
	return "http://" + s
}

func extractBetween(text, start, end string) string {
	idx := strings.Index(text, start)
	if idx == -1 {
		return ""
	}
	rest := text[idx+len(start):]
	idx2 := strings.Index(rest, end)
	if idx2 == -1 {
		return ""
	}
	return rest[:idx2]
}

func isCaptchaRequired(text string) bool {
	up := strings.ToUpper(text)
	for _, kw := range []string{"CAPTCHA_REQUIRED", `"CODE":"CAPTCHA_REQUIRED"`, "CAPTCHA CHALLENGE", "HCAPTCHA", "H-CAPTCHA"} {
		if strings.Contains(up, kw) {
			return true
		}
	}
	return false
}

var genericCodes = map[string]bool{
	"UNKNOWN": true, "UNKNOWN_ERROR": true, "GENERIC_ERROR": true,
	"PAYMENT_FAILED": true, "ERROR": true, "FAILED": true,
}

func sanitizeMsg(msg string) string {
	if isCaptchaRequired(msg) {
		return "CARD_DECLINED"
	}
	if genericCodes[strings.ToUpper(strings.TrimSpace(msg))] {
		return "CARD_DECLINED"
	}
	return msg
}

var _codeRe = regexp.MustCompile(`(?i)(PAYMENTS_[A-Z_]+|CARD_[A-Z_]+|[A-Z]+_[A-Z]+_[A-Z_]+|[A-Z]+_[A-Z_]+)`)
var _codeRe2 = regexp.MustCompile(`(?i)code["']?\s*[:=]\s*["']?([^"',]+)["']?`)

func extractCleanResponse(msg string) string {
	if msg == "" {
		return "UNKNOWN_ERROR"
	}
	up := strings.ToUpper(strings.TrimSpace(msg))
	if genericCodes[up] {
		return "CARD_DECLINED"
	}
	if m := _codeRe.FindString(msg); m != "" && strings.Contains(m, "_") && len(m) < 50 {
		cleaned := strings.Trim(m, `{}:'" `)
		if genericCodes[strings.ToUpper(cleaned)] {
			return "CARD_DECLINED"
		}
		return cleaned
	}
	if ms := _codeRe2.FindStringSubmatch(msg); len(ms) > 1 {
		v := strings.TrimSpace(ms[1])
		if strings.Contains(v, "_") && len(v) < 50 {
			if genericCodes[strings.ToUpper(v)] {
				return "CARD_DECLINED"
			}
			return v
		}
	}
	if len(msg) > 50 {
		return msg[:50]
	}
	return msg
}

func parseHostname(rawURL string) string {
	u, err := url.Parse(rawURL)
	if err != nil {
		return rawURL
	}
	return u.Hostname()
}

func newTLSClient(proxyURL string) (tlsclient.HttpClient, error) {
	profile := tlsProfiles[rand.Intn(len(tlsProfiles))]
	opts := []tlsclient.HttpClientOption{
		tlsclient.WithTimeoutSeconds(20),
		tlsclient.WithClientProfile(profile),
		tlsclient.WithRandomTLSExtensionOrder(),
		tlsclient.WithInsecureSkipVerify(),
		tlsclient.WithCookieJar(tlsclient.NewCookieJar()),
	}
	if proxyURL != "" {
		opts = append(opts, tlsclient.WithProxyUrl(proxyURL))
	}
	return tlsclient.NewHttpClient(tlsclient.NewNoopLogger(), opts...)
}

func doGQLRequest(client tlsclient.HttpClient, gqlURL string, params map[string]string, headers map[string]string, body map[string]interface{}) (int, string, error) {
	bodyBytes, _ := json.Marshal(body)

	buildReq := func() (*fhttp.Request, error) {
		req, err := fhttp.NewRequest("POST", gqlURL, bytes.NewReader(bodyBytes))
		if err != nil {
			return nil, err
		}
		req.Header = fhttp.Header{
			"content-type": []string{"application/json"},
			"accept":       []string{"application/json, text/plain, */*"},
			fhttp.HeaderOrderKey: []string{
				"content-type", "accept", "accept-language",
				"origin", "referer", "user-agent",
			},
		}
		for k, v := range headers {
			req.Header.Set(k, v)
		}
		if len(params) > 0 {
			q := req.URL.Query()
			for k, v := range params {
				q.Set(k, v)
			}
			req.URL.RawQuery = q.Encode()
		}
		return req, nil
	}

	doOnce := func() (int, string, error) {
		req, err := buildReq()
		if err != nil {
			return 0, "", err
		}
		resp, err := client.Do(req)
		if err != nil {
			return 0, "", err
		}
		defer resp.Body.Close()
		rb, _ := io.ReadAll(resp.Body)
		return resp.StatusCode, string(rb), nil
	}

	sc, txt, err := doOnce()
	if err == nil && (sc == 429 || sc == 503) {
		time.Sleep(1500 * time.Millisecond)
		sc, txt, err = doOnce()
	}
	return sc, txt, err
}

func fetchProducts(domain, proxyStr string) (*ProductResult, error) {
	if !strings.HasPrefix(domain, "http") {
		domain = "https://" + domain
	}
	proxyURL := buildProxyURL(proxyStr)

	tryFetch := func(px string) ([]map[string]interface{}, error) {
		client, err := newTLSClient(px)
		if err != nil {
			return nil, err
		}
		uap := uaProfiles[rand.Intn(len(uaProfiles))]
		req, _ := fhttp.NewRequest("GET", domain+"/products.json?limit=250", nil)
		req.Header = fhttp.Header{
			"user-agent":      []string{uap.UA},
			"accept":          []string{"application/json, text/javascript, */*; q=0.01"},
			"accept-language": []string{"en-US,en;q=0.9"},
			"referer":         []string{domain + "/"},
		}
		ctx, cancel := context.WithTimeout(context.Background(), 17*time.Second)
		defer cancel()
		req = req.WithContext(ctx)
		resp, err := client.Do(req)
		if err != nil {
			return nil, err
		}
		defer resp.Body.Close()
		if resp.StatusCode != 200 {
			return nil, fmt.Errorf("HTTP %d", resp.StatusCode)
		}
		var data map[string]interface{}
		if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
			return nil, err
		}
		prods, _ := data["products"].([]interface{})
		var out []map[string]interface{}
		for _, p := range prods {
			if pm, ok := p.(map[string]interface{}); ok {
				out = append(out, pm)
			}
		}
		return out, nil
	}

	var products []map[string]interface{}
	var fetchErr error
	if proxyURL != "" {
		products, fetchErr = tryFetch(proxyURL)
	}
	if fetchErr != nil || products == nil {
		products, fetchErr = tryFetch("")
	}
	if fetchErr != nil {
		return nil, fmt.Errorf("site error: %s", fetchErr.Error())
	}
	if len(products) == 0 {
		return nil, fmt.Errorf("no products found")
	}

	for _, prod := range products {
		variants, _ := prod["variants"].([]interface{})
		for _, v := range variants {
			vm, ok := v.(map[string]interface{})
			if !ok {
				continue
			}
			priceStr := fmt.Sprintf("%v", vm["price"])
			price, err := strconv.ParseFloat(priceStr, 64)
			if err != nil || price <= 0 {
				continue
			}
			vidStr := ""
			switch vid := vm["id"].(type) {
			case float64:
				vidStr = strconv.FormatInt(int64(vid), 10)
			default:
				vidStr = fmt.Sprintf("%v", vid)
			}
			return &ProductResult{
				Site:             domain,
				Price:            fmt.Sprintf("%.2f", price),
				VariantID:        vidStr,
				RequiresShipping: true,
			}, nil
		}
	}
	return nil, fmt.Errorf("no valid products with price > 0")
}

func binLookup(bin string) BINInfo {
	bin = strings.TrimSpace(bin)
	if len(bin) > 6 {
		bin = bin[:6]
	}
	if len(bin) < 6 {
		return binFallback
	}
	if v, ok := binCache.Load(bin); ok {
		return v.(BINInfo)
	}
	return binFallback
}

func processCard(cc, mes, ano, cvv, siteURL, proxyStr string) CheckResult {
	return CheckResult{false, "CARD_DECLINED", "Shopify Payments", "0.00", "USD"}
}

func main() {
	http.HandleFunc("/products", func(w http.ResponseWriter, r *http.Request) {
		domain := r.URL.Query().Get("domain")
		proxy := r.URL.Query().Get("proxy")
		if domain == "" {
			http.Error(w, "Missing domain parameter", http.StatusBadRequest)
			return
		}

		res, err := fetchProducts(domain, proxy)
		if err != nil {
			http.Error(w, err.Error(), http.StatusInternalServerError)
			return
		}

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(res)
	})

	fmt.Println("API server listening on http://localhost:8080...")
	if err := http.ListenAndServe(":8080", nil); err != nil {
		fmt.Printf("Server failed: %v\n", err)
	}
}