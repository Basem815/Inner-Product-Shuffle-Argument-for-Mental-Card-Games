package preprocessing

import (
	"crypto/rand"
	"fmt"
	"math/big"
	"os"
)


type PublicParameters struct {
	p *big.Int
    q *big.Int
    g *big.Int
    h *big.Int
    u *big.Int
    vec_g []*big.Int
    vec_h []*big.Int
}

// security_param should give the desired bit length of q
func generatePrimes(security_param int) (prime_p, prime_q *big.Int){
    
    for {
        q, err := rand.Prime(rand.Reader, security_param)
        if err != nil {
            panic(err)
        }
        // p = 2*R*q + 1 (Here R = 1)
        p := new(big.Int).Mul(q, big.NewInt(2))
        p.Add(p, big.NewInt(1))
        if p.ProbablyPrime(20){
            prime_q = q
            prime_p = p
            
            fmt.Printf("Prime p of length %v-bits and prime q of length %v-bits created \n", p.BitLen(), q.BitLen())
            break 
        }
    }
    return prime_p, prime_q
}

/* Given primes p, q such that p = 2q+1, find a generator of the subgroup of Z_p* with order q
    - Pick a random element h of Z_p*
    - Compute g = h^{p-1/q}                 // In our case it's  h^2 mod p
        - If g != 1, then g is a generator of the group G with order q
            - The probability that g = 1 will be 1/q so we are very likely to get a usable generator
*/
func generators(p, q *big.Int, numbOfGens int) ([]*big.Int){
    generators := []*big.Int{}
    not_generators := []*big.Int{}
    x := big.NewInt(0)
    x.SetInt64(int64(numbOfGens))
    /* Because the number of generators is phi(phi(p)) = phi(p-1) = q-1
        x below is the number of generators*/
    if q.Cmp(x) <= 0 {
        fmt.Printf("Cannot have more generators than the number of elements in the list\n")
        os.Exit(-1)
    } 
    h, _ := rand.Int(rand.Reader, new(big.Int).Sub(p, big.NewInt(1))) 
    h.Add(h, big.NewInt(1))
    h_pow_2 := new(big.Int).Exp(h, big.NewInt(2), p)
    // Probability of the statment below being true is 1/q
    for h_pow_2.Cmp(big.NewInt(1)) == 0{
        not_generators = append(not_generators, h_pow_2)
        h, _ = rand.Int(rand.Reader, new(big.Int).Sub(p, big.NewInt(1))) 
        h.Add(h, big.NewInt(1))

        h_pow_2 = new(big.Int).Exp(h, big.NewInt(2), p)
    }
    generators = append(generators, h_pow_2)
    outer:
    for len(generators) < numbOfGens {  
        h, _ = rand.Int(rand.Reader, new(big.Int).Sub(p, big.NewInt(1))) 
        h.Add(h, big.NewInt(1))
        h_pow_2 = new(big.Int).Exp(h, big.NewInt(2), p)
        for _, x := range generators{
            // If generator already accounted for, skip
            if x.Cmp(h_pow_2) == 0{
                continue outer 
            }
        }
        for _, x := range not_generators{
            // If value already tried, skip
            if x.Cmp(h_pow_2) == 0{
                continue outer 
            }
        }
        if h_pow_2.Cmp(big.NewInt(1)) == 0{
            not_generators = append(not_generators, h_pow_2)
        }else{
            generators = append(generators, h_pow_2)
        }
    }
    return generators
}

func Setup(security_param, n int, securityParamFixed bool) (pp PublicParameters) {
    // timeSetup := time.Now()
    
    p, q := new(big.Int), new(big.Int)
    if !securityParamFixed{
        p, q = generatePrimes(security_param)
    }else{
        // Example of 2048-bit values
        qStr := "27802772160381005603525238449936779676506810463330539006996504682301728141520011253644431110183491610476325972813074367063538949431409398682013091180613022925797915691008603888988795609574458107337437571168952560232087715109431347214100769721511887670808990946094517500954104434212349587440733400726960469279997760970506765088547881928238638857498141331134519566658371916794886713960684286999367495634582522130603122206695966250960803999715070306896398801719504939693111581581730186999512487573684533364448655457110845483832871678083210856603366669667438779670626746014744946076825547837085354572617969021318997314643"
        pStr := "55605544320762011207050476899873559353013620926661078013993009364603456283040022507288862220366983220952651945626148734127077898862818797364026182361226045851595831382017207777977591219148916214674875142337905120464175430218862694428201539443023775341617981892189035001908208868424699174881466801453920938559995521941013530177095763856477277714996282662269039133316743833589773427921368573998734991269165044261206244413391932501921607999430140613792797603439009879386223163163460373999024975147369066728897310914221690967665743356166421713206733339334877559341253492029489892153651095674170709145235938042637994629287"
        q.SetString(qStr, 10)
        p.SetString(pStr, 10)
    }
   

    

    generators := generators(p, q, 2*n+3)  // First 3 reserved for g, h, u and  remaining 2n for vec_g, vec_h
    return PublicParameters{
    	g:     generators[0],
        h:     generators[1],
        u :    generators[2],
    	p:     p,
        q:     q,
    	vec_g: generators[3 : n+3],
    	vec_h: generators[n+3:],
    }
}

func (pp PublicParameters) GetGeneratorG() (*big.Int) {
    return pp.g
}
func (pp *PublicParameters) SetGeneratorG(new_g *big.Int) () {
    pp.g = new_g
}
func (pp PublicParameters) GetGeneratorH() (*big.Int) {
    return pp.h
}
func (pp *PublicParameters) SetGeneratorH(new_h *big.Int) () {
    pp.h = new_h
}
func (pp PublicParameters) GetGeneratorU() (*big.Int) {
    return pp.u
}
func (pp PublicParameters) GetGeneratorsVec_G() ([]*big.Int) {
    return pp.vec_g
}
func (pp PublicParameters) GetGeneratorsVec_H() ([]*big.Int) {
    return pp.vec_h
}
func (pp PublicParameters) GetPrimeP() (*big.Int) {
    return pp.p
}
func (pp PublicParameters) GetPrimeQ() (*big.Int) {
    return pp.q
}
    
