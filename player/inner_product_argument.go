package player

import (
	"fmt"
	"main/preprocessing"
	"math/big"
	"os"
	"sync"
)

// Raises each component of vec_g to the power x
func vec_power_scalar(pp preprocessing.PublicParameters, vec_g []*big.Int, x *big.Int) []*big.Int{
	resultant_g := []*big.Int{}
	for _, val := range vec_g{
		g_i_pow_x := new(big.Int).Exp(val, x, pp.GetPrimeP())
		resultant_g = append(resultant_g, g_i_pow_x)
	}
	return resultant_g
}

// Component-wise multiplication of GROUP elements 
func vec_mul_vec(pp preprocessing.PublicParameters, a, b []*big.Int) []*big.Int{
	if len(a) != len(b){
		fmt.Printf("Oh no! slice A (len: %v) does not appear to have the same size as slice B (len %v) ", len(a), len(b))
		os.Exit(-1)
	}
	result := []*big.Int{}
	for i, elt := range b{
		prod := new(big.Int).Mul(elt, a[i])
		prod.Mod(prod, pp.GetPrimeP())
		result = append(result, prod )
	}
	return result 	
}


func isPowerOfTwo(n int) bool {
	return n > 0 && (n&(n-1)) == 0
}



func (prover *Prover) Protocol_one(pp preprocessing.PublicParameters, vec_g, vec_h []*big.Int, verifiers []Player, com_P *big.Int, powerArg bool, wg *sync.WaitGroup  ) {
	defer wg.Done()
	prime_p := pp.GetPrimeP()
	prime_q := pp.GetPrimeQ()
	gen_u := pp.GetGeneratorU()
	var a  []*big.Int
	var b  []*big.Int
	if !powerArg {
		a = prover.l_x
		b = prover.r_x
	}else{
		a = prover.l_w_x
		b = prover.r_w_x
	}
	// Append vectors until a power of 2
	for !isPowerOfTwo(len(a)) {
		a = append(a, big.NewInt(0))
		b = append(b, big.NewInt(0))
		vec_g = append(vec_g, pp.GetGeneratorG())
		vec_h = append(vec_h, pp.GetGeneratorG())		// Doesn't matter what the value is as it's power will be 0 anyways
	}
	c := innerProduct(pp, a, b)			// Equivalent to t as given in the paper
	x := CombinedChallenge(pp, verifiers)
	x_times_c := new(big.Int).Mul(x, c)
	x_times_c.Mod(x_times_c, prime_q)
	u_pow_xc := new(big.Int).Exp(gen_u, x_times_c, prime_p)
	com_P_prime := new(big.Int).Mul(com_P, u_pow_xc)
	com_P_prime.Mod(com_P_prime, prime_p)
	u_pow_x := new(big.Int).Exp(gen_u, x, prime_p)
	prover.protocol_two(pp, vec_g, vec_h, u_pow_x, com_P_prime, a, b, verifiers)
}		

func (prover *Prover) protocol_two(pp preprocessing.PublicParameters, vec_g, vec_h []*big.Int, u, p *big.Int, a, b []*big.Int,  verifiers []Player) {
	prime_p := pp.GetPrimeP()
	prime_q := pp.GetPrimeQ()
	if len(a) == 1{
		// P sends a,b to V
		// V comutes c = a*b and checks if P = (g^a)(h^b)(u^c)
		for _, verifier := range verifiers{
			if !verifier.finalCheck(pp, vec_g, vec_h, u, p, a, b) {
				fmt.Printf("Final inner product not equal to given P. Exiting \n ")
				os.Exit(-1)
			}
		}
	}else{
		/* Step 1: Prover: 
				- n' = n//2
				- c_L = < a[:n'], b[n':] >
				- c_R = < a[n':], b[:n'] >
				- L =  g[n':]^(a[:n']) * h[:n']^(b[n':]) * u^(c_L)
				- R =  g[:n']^(a[n':]) * h[n':]^(b[:n']) * u^(c_R)
		*/
		n_prime := len(a)/2
		c_L := innerProduct(pp, a[:n_prime], b[n_prime:])
		c_R := innerProduct(pp, a[n_prime:], b[:n_prime])
		l_tmp1 := genPowerVec(pp, vec_g[n_prime:], a[:n_prime])
		l_tmp2 := genPowerVec(pp, vec_h[:n_prime], b[n_prime:])
		l_tmp3 := new(big.Int).Exp(u, c_L, prime_p)
		l := new(big.Int).Mul(l_tmp1, l_tmp2)
		l.Mod(l, prime_p)
		l.Mul(l, l_tmp3)
		l.Mod(l, prime_p)

		r_tmp1 := genPowerVec(pp, vec_g[:n_prime], a[n_prime:])
		r_tmp2 := genPowerVec(pp, vec_h[n_prime:], b[:n_prime])
		r_tmp3 := new(big.Int).Exp(u, c_R, prime_p)
		r := new(big.Int).Mul(r_tmp1, r_tmp2)
		r.Mod(r, prime_p)
		r.Mul(r, r_tmp3)
		r.Mod(r, prime_p)
		
		// Step 2: Verifier: Sends challenge x 
		x := CombinedChallenge(pp, verifiers)
		x_pow_2 := new(big.Int).Exp(x, big.NewInt(2), prime_q)
		inverse_x_pow_2 := new(big.Int).ModInverse(x_pow_2, prime_q)
		/* Step 3: Prover and verifier
			- g' = g[:n']^(x^{-1}) o g[n':]^(x)
			- h' = h[:n']^(x) o h[n':]^(x^{-1})
			- P' = L^{x^2} * P * R^{x^{-2}}
		*/
		inverse_x := new(big.Int).ModInverse(x, prime_q)
		g_prime_t1 := vec_power_scalar(pp, vec_g[:n_prime], inverse_x)
		g_prime_t2 := vec_power_scalar(pp, vec_g[n_prime:], x)
		g_prime := vec_mul_vec(pp, g_prime_t1, g_prime_t2)

		h_prime_t1 := vec_power_scalar(pp, vec_h[:n_prime], x)
		h_prime_t2 := vec_power_scalar(pp, vec_h[n_prime:], inverse_x)
		h_prime := vec_mul_vec(pp, h_prime_t1, h_prime_t2)

		p_prime_t1 := new(big.Int).Exp(l, x_pow_2, prime_p)
		p_prime_t2 := new(big.Int).Exp(r, inverse_x_pow_2, prime_p)

		p_prime := new(big.Int).Mul(p_prime_t1, p)
		p_prime.Mod(p_prime, prime_p)
		p_prime.Mul(p_prime, p_prime_t2)
		p_prime.Mod(p_prime, prime_p)
		
		/* Step 4: Prover computes
			- a' = a[:n'].x + a[n':].(x^{-1})
			- b' = b[:n'].(x^{-1}) + b[n':].(x)
		*/
		a_prime_t1 := multiplySliceByScalar(pp, a[:n_prime], x)
		a_prime_t2 := multiplySliceByScalar(pp, a[n_prime:], inverse_x)
		a_prime := addTwoSlices(pp, a_prime_t1, a_prime_t2)
		b_prime_t1 := multiplySliceByScalar(pp, b[:n_prime], inverse_x)
		b_prime_t2 := multiplySliceByScalar(pp, b[n_prime:], x)
		b_prime := addTwoSlices(pp, b_prime_t1, b_prime_t2)
		
		// Recursive step 
		prover.protocol_two(pp, g_prime, h_prime, u, p_prime, a_prime, b_prime, verifiers  )
	}

}

func (player *Player) finalCheck(pp preprocessing.PublicParameters, vec_g, vec_h []*big.Int, u, p *big.Int, a, b []*big.Int) bool {
	prime_p := pp.GetPrimeP()
	prime_q := pp.GetPrimeQ()
	c := new(big.Int).Mul(a[0],b[0])
	c.Mod(c, prime_q)
	final_p_t1 := new(big.Int).Exp(vec_g[0], a[0], prime_p)
	final_p_t2 := new(big.Int).Exp(vec_h[0], b[0], prime_p)
	final_p_t3 := new(big.Int).Exp(u, c, prime_p)
	final_p := new(big.Int).Mul(final_p_t1, final_p_t2)
	final_p.Mod(final_p, prime_p)
	final_p.Mul(final_p, final_p_t3)
	final_p.Mod(final_p, prime_p)
	return p.Cmp(final_p) == 0
}