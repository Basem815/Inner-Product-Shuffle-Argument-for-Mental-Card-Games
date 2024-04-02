package player

import (
	"fmt"
	"main/preprocessing"
	"math/big"
	"os"
	"sync"
)

// Multiplies each component of slice with the multiplier
func multiplySliceByScalar(pp preprocessing.PublicParameters, slice []*big.Int, multiplier *big.Int) []*big.Int{
	result := make([]*big.Int, len(slice))
	for i, val := range slice {
		prod := new(big.Int).Mul(val, multiplier)
		prod.Mod(prod, pp.GetPrimeQ())
		result[i] = prod 
	}
	return result 
}

// Multiplies two slices component wise and adds the results
func innerProduct(pp preprocessing.PublicParameters, sliceA, sliceB []*big.Int) *big.Int {
	if len(sliceA) != len(sliceB){
		fmt.Printf("Oh no! slice A (len: %v) does not appear to have the same size as slice B (len %v) ", len(sliceA), len(sliceB))
		os.Exit(-1)
	}
	result := big.NewInt(0)
	for i, val := range(sliceA){
		prod := new(big.Int).Mul(val, sliceB[i])
		prod.Mod(prod, pp.GetPrimeQ())
		result.Add(result, prod)
		result.Mod(result, pp.GetPrimeQ())
	}
	return result
}

func addTwoSlices(pp preprocessing.PublicParameters, slice1, slice2 []*big.Int) []*big.Int {
	if len(slice1) != len(slice2){
		fmt.Printf("Oh no! slice 1 (len: %v) does not appear to have the same size as slice 2 (len %v) ", len(slice1), len(slice2))
		os.Exit(-1)
	}
	result := []*big.Int{}
	for i, elt := range slice2{
		prod := new(big.Int).Add(elt, slice1[i])
		prod.Mod(prod, pp.GetPrimeQ())
		result = append(result, prod )
	}
	return result 
}

func subTwoSlices(pp preprocessing.PublicParameters, slice1, slice2 []*big.Int) []*big.Int {
	if len(slice1) != len(slice2){
		fmt.Printf("Oh no! slice1 (len: %v) does not appear to have the same size as slice2 (len %v) ", len(slice1), len(slice2))
		os.Exit(-1)
	}
	result := []*big.Int{}
	for i, elt := range slice1{
		prod := new(big.Int).Sub(elt, slice2[i])
		prod.Mod(prod, pp.GetPrimeQ())
		result = append(result, prod )
	}
	return result 
}

// Component wise multiplication
func MultiplyTwoSlices(pp preprocessing.PublicParameters, slice1, slice2 []*big.Int) []*big.Int {
	if len(slice1) != len(slice2){
		fmt.Printf("Oh no! slice_1 (len: %v) does not appear to have the same size as slice_2 (len %v) ", len(slice1), len(slice2))
		os.Exit(-1)
	}
	result := []*big.Int{}
	for i, elt := range slice2{
		prod := new(big.Int).Mul(elt, slice1[i])
		prod.Mod(prod, pp.GetPrimeQ())
		result = append(result, prod )
	}
	return result 	
}



/* Input: a vector of generators and a vector of powers of equal size 
	Output: Single *big.Int value representing the product of each generator raised to each power
		e.g: vec_g = (g_1, g_2) & vec_a = (a_1, a_2) ---> return (g_1)^(a_1) * (g_2)^(a_2) */
func genPowerVec(pp preprocessing.PublicParameters, vec_gens_g, vec_a []*big.Int) *big.Int{
	p := pp.GetPrimeP()
	
	if len(vec_gens_g) != len(vec_a){
		fmt.Println("The vectors should be of the same length")
		os.Exit(-1)
	}
	product := big.NewInt(1)
    for idx := range  vec_a{
			gi_pow_ai := new(big.Int).Exp(vec_gens_g[idx], vec_a[idx],p )
        	product.Mul(product, gi_pow_ai)
			product.Mod(product, p)
    }
	
	return product
}

// IP for interactive protocol
func (prover *Prover)IP(pp preprocessing.PublicParameters,  verifiers []Player, n int, input_ciphertexts, output_ciphertexts [][2]*big.Int, with_inner_product bool) {
	// timeIP := time.Now()
	// verifier := verifiers[0]
	
	wg := sync.WaitGroup{}
	wg.Add(3)
	fmt.Printf("Start of the shuffle argument by player %v \n", prover.Id)
	p := pp.GetPrimeP() 
	q := pp.GetPrimeQ()
	g := pp.GetGeneratorG()
	vec_g := pp.GetGeneratorsVec_G()
	vec_h := pp.GetGeneratorsVec_H()		// For inner product
	h := pp.GetGeneratorH()


	vec_b := []*big.Int{}			// x-component of input ciphtexts
	vec_c := []*big.Int{}			// y-component of input ciphtexts
	for _, ciphtext := range input_ciphertexts{
		vec_b = append(vec_b, ciphtext[0])
		vec_c = append(vec_c, ciphtext[1])
	}

	// Step 1: Prover runs the CRSCheck and exits if it does not return true
	prover.CRSCheck(pp)

	// Step 2: V sends two random challenges r, u from Z*_q

	r ,u := CombinedChallenge(pp, verifiers), CombinedChallenge(pp, verifiers) 

	/* Step 3: 
		(i)  Both parties compute vec_k = (r-u^i) for i = 1 .. n
		(ii) Both parties compute commitments A_{r,b} and A_{r,c} wrt outputs of the shuffle (b', c')
		(iii) Define k_hat := prod(k_i) and k* as sum(k_i)
	*/
	// (i):	
	k := []*big.Int{}
	for i :=1 ; i <= n; i++ {
		pow := new(big.Int).Exp(u, big.NewInt(int64(i)), q)
		k_i := new(big.Int).Sub(r, pow)
		k_i.Mod(k_i,q)
		k = append(k, k_i)
	}
	// (ii): 
	A_rb := big.NewInt(1)
	A_rc := big.NewInt(1)
	for i, ciphtxt := range output_ciphertexts{
		pow_a_rb, pow_a_rc := new(big.Int).Exp(ciphtxt[0], k[i], p), new(big.Int).Exp(ciphtxt[1], k[i], p)
		A_rb.Mul(A_rb, pow_a_rb)
		A_rb.Mod(A_rb, p)
		A_rc.Mul(A_rc, pow_a_rc)
		A_rc.Mod(A_rc, p)
	}
	// (iii)
	k_prod := big.NewInt(1)
	k_sum := big.NewInt(0)
	for _, val := range k {
		k_prod.Mul(k_prod, val)
		k_prod.Mod(k_prod, q)
		k_sum.Add(k_sum, val)
		k_sum.Mod(k_sum, q)	
	}

	/* Step 4: Only prover
		(i): Compute a_r = (s*k_{pi^{-1}(1)}, ...,  s*k_{pi^{-1}(n)})
		(ii): Compute a_l = (1, s*k_{pi^{-1}(1)}, s^{2}*k_{pi^{-1}(1)}*k_{pi^{-1}(2)},  ...,  s^{n-1}*k_{pi^{-1}(1)}*...*k_{pi^{-1}(n-1)})
		(iii): Generate rand values alpha, beta, rho_b, rho_c from Z_q
		(iv): Generate blinding vectors s_L and s_R of size n from Z_q

		Power_argument:
			(i): a_{R,w} = {s, s, ... ,s}
			(ii): a_{L,w} = (1, s, s^2, ..., s^{n-1})
			(iii):  Generate rand values alpha_w, beta_w from Z_q
			(iv): Generate blinding vectors s_{L,w} and s_{R,w} of size n from Z_q
	*/
	// (i) & (ii)
	prover.Step4A(pp, k)
	// (iii) & (iv)
	prover.Step4B(pp, n)
	prover.Step4Power(pp, n)

	/* Step 5:  Prover to Verifier (Group elements so mod p)
		 (i)   A_L =g^{a_L}h^{alpha}
		 (ii)  S_L =g^{s_L}h^{beta} 
		 (iii) S_{R,b} = b^{s_R}h^{rho_b} 
		 (iv)  S_{R,c} = c^{s_R}h^{rho_c}

		 Power Arg: 
		 	(i): A_w = g^{a_{L,w}}h^{a_{R,w}}h^{alpha_w}
			(ii): S_w = g^{s_{L,w}}h^{s_{R,w}}h^{beta_w}
	*/
	A_L, S_L, S_rb, S_rc := prover.Step5(pp, vec_b, vec_c)
	A_w, S_w := prover.Step5Power(pp)

	/* Step 6: Verifier sends two challengs y, z*/
	w, y, z := CombinedChallenge(pp, verifiers), CombinedChallenge(pp, verifiers), CombinedChallenge(pp, verifiers)

	/*  Step 7: Both Prover and Verifier compute:
			(i)   y^{n} =(1, y, y^2, ..., y^{n-1})
			(ii)  y^{n-2}_z = (z, 1, ..., y^{n-2})
			(iii) delta(y, z)=  <z^3*y^{-n}, y^{n-2}_z > - z		 Should be plus z 

			Power Argument: 
				(i): w^{n} = (1, w, ..., w^{n-1})
				(ii): w_0^{n-1} = (0, 1, w, ..., w^{n-2})
				(iii): delta(y,z,w) = -z(2+z+(n-1)y^{-1}) + (y^{1} - w )SUM_{i=0}^{n-2}(wy)^{i}
	*/
	// (i) & (ii)
	vec_y := []*big.Int{}
	vec_y = append(vec_y, big.NewInt(1))				// y^{n} =(1, y, y^2, ..., y^{n-1})

	// From bulletproofs: k^{-n} = (k^{-1})^n  where k^{-1} is the inverse of k
	inverse_of_y := new(big.Int).ModInverse(y, q)
	vec_y_inverse := []*big.Int{} 						// y^{-n} = (1, y^{-1}, ... , y^{-n+1})
	vec_y_inverse = append(vec_y_inverse, big.NewInt(1))
	
	vec_y_z := []*big.Int{}								// y^{n-2}_z = (z, 1, ..., y^{n-2})
	vec_y_z = append(vec_y_z, z)
	vec_y_z = append(vec_y_z, big.NewInt(1))	

	
	// Power Argument 
	vec_w :=  []*big.Int{}
	vec_w = append(vec_w, big.NewInt(1))				// vec_w = (1, w, ..., w^{n-1})
	vec_w_0 := []*big.Int{}								// w_0^{n-1} = (0, 1, w, ..., w^{n-2})
	vec_w_0 = append(vec_w_0, big.NewInt(0))
	vec_w_0 = append(vec_w_0, big.NewInt(1))	
	

	for i:=1; i < n; i++ {
		pow := new(big.Int).Exp(y, big.NewInt(int64(i)), q)
		pow_inv := new(big.Int).Exp(inverse_of_y, big.NewInt(int64(i)), q)
		pow_w := new(big.Int).Exp(w, big.NewInt(int64(i)), q)
		vec_y = append(vec_y, pow)
		vec_w = append(vec_w, pow_w)
		vec_y_inverse = append(vec_y_inverse, pow_inv)
		if i < n-1 {
			vec_y_z = append(vec_y_z, pow)
			vec_w_0 = append(vec_w_0, pow_w)
		}
	} 
	
	// (iii)
	z_3 := new(big.Int).Exp(z, big.NewInt(3), q)
	vec_z3_times_yn := multiplySliceByScalar(pp, vec_y_inverse, z_3)

	delta_y_z := innerProduct(pp, vec_z3_times_yn, vec_y_z)
	delta_y_z.Add(delta_y_z, z)
	delta_y_z.Mod(delta_y_z, q)
	 

	// Power Argument (iii): delta(y,z,w) = -z(2+z+(n-1)y^{-1}) + (y^{-1} - w )SUM_{i=0}^{n-2}(wy)^{i}
	tmpCal := big.NewInt(2)
	tmpCal.Add(tmpCal, z)
	tmpCal.Mod(tmpCal, q)
	tmpCal2 := new(big.Int).Mul(inverse_of_y, big.NewInt(int64(n-1)))
	tmpCal2.Mod(tmpCal2, q)
	tmpCal.Add(tmpCal, tmpCal2)
	tmpCal.Mod(tmpCal, q)
	
	minus_z := new(big.Int).Mul(z, big.NewInt(-1))
	minus_z.Mod(minus_z, q)
	tmpCal.Mul(tmpCal, minus_z)
	tmpCal.Mod(tmpCal, q)

	sumPow_tmp := big.NewInt(1)
	w_times_y :=  new(big.Int).Mul(w,y)
	w_times_y.Mod(w_times_y, q)
	for i:= 1; i <= n-2; i++ {
		prod := new(big.Int).Exp(w_times_y, big.NewInt(int64(i)), q)
		sumPow_tmp.Add(sumPow_tmp, prod)
		sumPow_tmp.Mod(sumPow_tmp, q)
	}
	y_inverse_min_w := new(big.Int).Sub(inverse_of_y, w)
	y_inverse_min_w.Mod(y_inverse_min_w, q)
	y_inverse_min_w.Mul(y_inverse_min_w, sumPow_tmp)
	y_inverse_min_w.Mod(y_inverse_min_w, q)

	delta_w_y_z := new(big.Int).Add(tmpCal, y_inverse_min_w)
	delta_w_y_z.Mod(delta_w_y_z, q)

	/* Step 8: Only prover
		(i)   l(X) = a_l + z^3y^{-n} + s_l * X^2
		(ii)  r(X) =(a_R*X +s_R*X^3) o (y_n) - X*(y^{n-2}_z)
		(iii) t(X) = <l(X) r(X) > = Sum(t_i*X^i)
		(iv)  t_1 = s^n * k^ * y^{n-1} + s*z^3 (k*) + delta(y,z) 	// - delta(y,z())
		(v)   tau_i <-- Z_p*  i = {3,5}
		(vi)  T_i = g^{t_i}*h^{tau_i}  i = {3,5}
		Added : 
		(vii) tau_1 := (sigma_v)*(z^3)*(k_sum) + (sigma_w)*(y^{n-1})*k_prod 

		Power Argument
			(i): l_w(X) = a_{l,w} + zy^{-n} + w^n - w_0^{n-1}y^{-1} + s_{l,w}X
			(ii): r_w(X) = y^n o (a_{R,w} + s_{R,w}X) - y_z^{n-1}
			(iii): t_w(X) = <l_w(X), r_w(X) > = Sum(t_{i,w}*X^i)
			(iv): t_{0,w} = s^{n}y^{n-1} + s( (wy)^{n-1} + nz) + delta(w,y,z)
			(v):  tau_{i,w} <-- Z_q*  i = {1,2}
			(vi)  T_i = g^{t_{i,w}}*h^{tau_{i,w}}  i = {1,2}
	*/
	
	T_3, T_5 := prover.Step8(pp, vec_y, vec_y_z, vec_z3_times_yn, k_sum, k_prod, delta_y_z, n)
	T_w_1, T_w_2 := prover.Step8Power(pp, vec_y, vec_y_inverse, vec_y_z, vec_w, vec_w_0, delta_w_y_z, n)

	// Step 9 : Verifier sends a challenge x
	x := CombinedChallenge(pp, verifiers)
	x_pow_2 := new(big.Int).Exp(x, big.NewInt(int64(2)), q)
	x_pow_3 := new(big.Int).Exp(x, big.NewInt(int64(3)), q)
	x_pow_5 := new(big.Int).Exp(x, big.NewInt(int64(5)), q)
	
	/*	 10. Prover to Verifier:
			(i)   l =l(x)		
			(ii)  r =r(x)	
			(iii) t =<l r>
			(iv)  tau_x= tau_1x + tau_3*x_3+ tau_5*x_5 
			(v)   mew_b = alpha + beta*(x^2) + rho_b*(x^3)
			(vi)  mew_c = alpha + beta*(x^2) + rho_c*(x^3)

			Power Argument
				(i): l_w = l_w(x)
				(ii): r_w = r_w(x)
				(iii): t_w = <l_w, r_w>
				(iv) tau_w_x = tau_w_0 + tau_w_1*x + tau_w_2 * x_2
				(v) mew_w = alpha_w + beta_w * x
	*/
	// (i) && (ii)
	t_x, tau_x, mew_b, mew_c := prover.Step10(pp, vec_y, vec_y_z, vec_z3_times_yn, x, n)
	l_x, r_x := prover.l_x, prover.r_x

	t_w_x, tau_w_x, mew_w := prover.Step10Pow(pp, vec_y, vec_y_z, vec_z3_times_yn, x, n)

	/* Step 11: Verifier makes the final checks 
			(i)   b_{i}* = b_i^{y-i}
			(ii)  c_{i}* = c_i^{y-i}
			(iii) g^{t_x} * h^{tau_x} =? V^{z^3*k_sum*x} * W^{y^{n-1}*k_prod*x} * g^{delta(y,z)*x} * (T_3)^{x^3} * (T_5)^{x^5}
			(iv)  h^{mew_b} * (vec_g)^{l(x)} * (b*)^r =? A_L * A{R,b}^x * S_L^{x^2} * S_{R,b}^{x^3} * (vec_g)^{z^3*vec_y^-n} * (b*)^{-x*vec_y_z}
			(v)   h^{mew_c} * (vec_g)^{l(x)} * (c*)^r =? A_L * A{R,c}^x * S_L^{x^2} * S_{R,c}^{x^3} * (vec_g)^{z^3*vec_y^-n} * (c*)^{-x*vec_y_z}
			(vi)  t =? <l, r>

			Power Argument
			(i): g^{t_{w,x}} * h^{tau_{w,x}} =? V^{(wy)^{n-1} + nz} * W^{y^{n-1}} * g^{delta(w, y,z)} * (T_w_1)^{x} * (T_w_2)^{x^2}
 	*/

	// (i) && (ii)
	vec_b_star := []*big.Int{}
	vec_c_star := []*big.Int{}
	vec_h_star := []*big.Int{}
	for i:= range vec_b{
		b_i_pow_y_inv := new(big.Int).Exp(vec_b[i], vec_y_inverse[i], p )
		c_i_pow_y_inv := new(big.Int).Exp(vec_c[i], vec_y_inverse[i], p )
		h_i_pow_y_inv := new(big.Int).Exp(vec_h[i], vec_y_inverse[i], p )
		
		vec_b_star = append(vec_b_star, b_i_pow_y_inv)
		vec_c_star = append(vec_c_star, c_i_pow_y_inv)
		vec_h_star = append(vec_h_star, h_i_pow_y_inv)
	}
	
	// (iii) : 
	lhs_tmp_1 := new(big.Int).Exp(g, t_x, p)
	lhs_tmp_2 := new(big.Int).Exp(h, tau_x, p)
	lhs_1 := new(big.Int).Mul(lhs_tmp_1, lhs_tmp_2)
	lhs_1.Mod(lhs_1, p)
	
	V, W := prover.PowerArgComs(pp, n)

	rhs_V_pow_tmp := new(big.Int).Mul(z_3, k_sum)
	rhs_V_pow_tmp.Mod(rhs_V_pow_tmp, q)
	rhs_V_pow_tmp.Mul(rhs_V_pow_tmp, x)
	rhs_V_pow_tmp.Mod(rhs_V_pow_tmp, q)
	rhs_V_pow := new(big.Int).Exp(V, rhs_V_pow_tmp, p)
	
	y_pow_n_min_1 := new(big.Int).Exp(y, big.NewInt(int64(n-1)), q)

	rhs_W_pow_tmp := new(big.Int).Mul(y_pow_n_min_1, k_prod)
	rhs_W_pow_tmp.Mod(rhs_W_pow_tmp, q)
	rhs_W_pow_tmp.Mul(rhs_W_pow_tmp, x)
	rhs_W_pow_tmp.Mod(rhs_W_pow_tmp, q)
	rhs_W_pow := new(big.Int).Exp(W, rhs_W_pow_tmp, p)

	rhs_g_pow_tmp := new(big.Int).Mul(delta_y_z, x)			
	rhs_g_pow_tmp.Mod(rhs_g_pow_tmp, q)			
	g_inverse := new(big.Int).ModInverse(g, p)
	rhs_g_pow := new(big.Int).Exp(g_inverse, rhs_g_pow_tmp, p)

	rhs_t3 := new(big.Int).Exp(T_3, x_pow_3, p)
	rhs_t5 := new(big.Int).Exp(T_5, x_pow_5, p)

	rhs := new(big.Int).Mul(rhs_V_pow, rhs_W_pow)
	rhs.Mod(rhs, p )
	rhs.Mul(rhs, rhs_g_pow)
	rhs.Mod(rhs, p )
	rhs.Mul(rhs, rhs_t3)
	rhs.Mod(rhs, p )
	rhs.Mul(rhs, rhs_t5)
	rhs.Mod(rhs, p )
	
	if lhs_1.Cmp(rhs) != 0 {
		fmt.Printf("verification 1 of step 11 failed \n")
		os.Exit(-1)
	}

	// Power argument
	lhs_tmp_w_1 := new(big.Int).Exp(g, t_w_x, p)
	lhs_tmp_w_2 := new(big.Int).Exp(h, tau_w_x, p)
	lhs_w_1 := new(big.Int).Mul(lhs_tmp_w_1, lhs_tmp_w_2)
	lhs_w_1.Mod(lhs_w_1, p)

	// V^{(wy)^{n-1} + nz} * W^{y^{n-1}} * g^{delta(w, y,z)} * (T_w_1)^{x} * (T_w_2)^{x^2}
	w_times_y_new := new(big.Int).Mul(w, y)
	w_times_y_new.Mod(w_times_y_new, q)
	rhs_V_w_pow_tmp := new(big.Int).Exp(w_times_y_new, big.NewInt(int64(n-1)), q)
	n_times_z := new(big.Int).Mul(z, big.NewInt(int64(n)))
	n_times_z.Mod(n_times_z, q)
	rhs_V_w_pow := new(big.Int).Add(rhs_V_w_pow_tmp, n_times_z)
	rhs_V_w_pow.Mod(rhs_V_w_pow, q)

	rhs_V_w := new(big.Int).Exp(V, rhs_V_w_pow, p)			// s [{(wy)^{n-1} + nz}]  sigma_v[{(wy)^{n-1} + nz}]

	rhs_W_w_pow := new(big.Int).Exp(y, big.NewInt(int64(n-1)), q)
	rhs_W_w := new(big.Int).Exp(W, rhs_W_w_pow, p)			// s^n[y^{n-1}]  sigma_w[y^{n-1}]
	rhs_g_w_1 := new(big.Int).Exp(g, delta_w_y_z, p)
	rhs_t_w_1 := new(big.Int).Exp(T_w_1, x, p)
	rhs_t_w_2 := new(big.Int).Exp(T_w_2, x_pow_2, p)
	
	rhs_w := new(big.Int).Mul(rhs_V_w, rhs_W_w)
	rhs_w.Mod(rhs_w, p )
	
	rhs_w.Mul(rhs_w, rhs_g_w_1)
	rhs_w.Mod(rhs_w, p )
	rhs_w.Mul(rhs_w, rhs_t_w_1)
	rhs_w.Mod(rhs_w, p )
	rhs_w.Mul(rhs_w, rhs_t_w_2)
	rhs_w.Mod(rhs_w, p )

	if lhs_w_1.Cmp(rhs_w) != 0 {
		fmt.Printf("verification 1 of (power argument) failed \n")
		os.Exit(-1)
	}

	// (iv)  h^{mew_b} * (vec_g)^{l(x)} * (b*)^r =? A_L * A{R,b}^x * S_L^{x^2} * S_{R,b}^{x^3} * (vec_g)^{z^3*vec_y^-n} * (b*)^{-x*vec_y_z}

	rhs_A_rb_pow_x := new(big.Int).Exp(A_rb, x, p)
	rhs_S_l_pow_x2 := new(big.Int).Exp(S_L, x_pow_2, p)
	rhs_S_rb_pow_x3 := new(big.Int).Exp(S_rb, x_pow_3, p)
	rhs_g_pow_z3yn := genPowerVec(pp, vec_g, vec_z3_times_yn)
	x_times_vec_y_z := multiplySliceByScalar(pp, vec_y_z, x)
	
	rhs_b_star_pow_minus_x_yz := big.NewInt(1)
	rhs_c_star_pow_minus_x_yz := big.NewInt(1)	// For part v (similar calculations)
	for i, elt := range x_times_vec_y_z {
		b_star_pow := new(big.Int).Exp(vec_b_star[i], elt, p)
		c_star_pow := new(big.Int).Exp(vec_c_star[i], elt, p)
		rhs_b_star_pow_minus_x_yz.Mul(rhs_b_star_pow_minus_x_yz, new(big.Int).ModInverse(b_star_pow, p) )
		rhs_b_star_pow_minus_x_yz.Mod(rhs_b_star_pow_minus_x_yz, p)
		rhs_c_star_pow_minus_x_yz.Mul(rhs_c_star_pow_minus_x_yz, new(big.Int).ModInverse(c_star_pow, p) )		// For part v
		rhs_c_star_pow_minus_x_yz.Mod(rhs_c_star_pow_minus_x_yz, p)										// For part v
	}
	rhs_2 := new(big.Int).Mul(A_L, rhs_A_rb_pow_x)
	rhs_2.Mod(rhs_2, p)
	rhs_2.Mul(rhs_2, rhs_S_l_pow_x2)
	rhs_2.Mod(rhs_2, p)
	rhs_2.Mul(rhs_2, rhs_S_rb_pow_x3)
	rhs_2.Mod(rhs_2, p)
	rhs_2.Mul(rhs_2, rhs_g_pow_z3yn)
	rhs_2.Mod(rhs_2, p)
	rhs_2.Mul(rhs_2, rhs_b_star_pow_minus_x_yz)
	rhs_2.Mod(rhs_2, p)

	lhs_h_pow_mew_b := new(big.Int).Exp(h, mew_b, p)
	h_pow_mew_b_inverse := new(big.Int).ModInverse(lhs_h_pow_mew_b, p)
	com_p_1 := new(big.Int).Mul(rhs_2,h_pow_mew_b_inverse)
	com_p_1.Mod(com_p_1, p)
	
	
	rhs_A_rc_pow_x := new(big.Int).Exp(A_rc, x, p)
	rhs_S_rc_pow_x3 := new(big.Int).Exp(S_rc, x_pow_3, p)
	
	rhs_3 := new(big.Int).Mul(A_L, rhs_A_rc_pow_x)
	rhs_3.Mod(rhs_3, p)
	rhs_3.Mul(rhs_3, rhs_S_l_pow_x2)
	rhs_3.Mod(rhs_3, p)
	rhs_3.Mul(rhs_3, rhs_S_rc_pow_x3)
	rhs_3.Mod(rhs_3, p)
	rhs_3.Mul(rhs_3, rhs_g_pow_z3yn)
	rhs_3.Mod(rhs_3, p)
	rhs_3.Mul(rhs_3, rhs_c_star_pow_minus_x_yz)
	rhs_3.Mod(rhs_3, p)

	lhs_h_pow_mew_c := new(big.Int).Exp(h, mew_c, p)
	h_pow_mew_c_inverse := new(big.Int).ModInverse(lhs_h_pow_mew_c, p)
	com_p_2 := new(big.Int).Mul(rhs_3,h_pow_mew_c_inverse)
	com_p_2.Mod(com_p_2, p)
	

	// Power Argument 

	rhs_s_w_pow_x := new(big.Int).Exp(S_w, x, p)
	rhs_g_w_pow_tmp := multiplySliceByScalar(pp, vec_y_inverse, z)
	rhs_g_w_pow_tmp2 := addTwoSlices(pp, rhs_g_w_pow_tmp, vec_w)
	rhs_g_w_pow_tmp3 := multiplySliceByScalar(pp, vec_w_0, vec_y_inverse[1])
	rhs_g_w_pow := subTwoSlices(pp, rhs_g_w_pow_tmp2, rhs_g_w_pow_tmp3)
	
	rhs_g_w_2 := genPowerVec(pp, vec_g, rhs_g_w_pow)

	rhs_y_star_pow_minus_yz := big.NewInt(1)	// For part v (similar calculations)
	for i, elt := range vec_y_z {
		h_star_pow := new(big.Int).Exp(vec_h_star[i], elt, p)
		rhs_y_star_pow_minus_yz.Mul(rhs_y_star_pow_minus_yz, new(big.Int).ModInverse(h_star_pow, p) )
		rhs_y_star_pow_minus_yz.Mod(rhs_y_star_pow_minus_yz, p)
	}

	rhs_w_2 := new(big.Int).Mul(A_w, rhs_s_w_pow_x)
	rhs_w_2.Mod(rhs_w_2, p)
	rhs_w_2.Mul(rhs_w_2, rhs_g_w_2)
	rhs_w_2.Mod(rhs_w_2, p)
	rhs_w_2.Mul(rhs_w_2, rhs_y_star_pow_minus_yz)
	rhs_w_2.Mod(rhs_w_2, p)

	lhs_h_pow_mew_w := new(big.Int).Exp(h, mew_w, p)
	h_pow_mew_w_inverse := new(big.Int).ModInverse(lhs_h_pow_mew_w, p)
	com_p_w := new(big.Int).Mul(rhs_w_2,h_pow_mew_w_inverse)
	com_p_w.Mod(com_p_w, p)
	

	
	if with_inner_product {
		
		go prover.Protocol_one(pp, vec_g, vec_b_star, verifiers, com_p_1, false, &wg)
		go prover.Protocol_one(pp, vec_g, vec_c_star, verifiers, com_p_2, false, &wg)
		
		// Product Arg
		go prover.Protocol_one(pp, vec_g, vec_h_star, verifiers, com_p_w, true, &wg)
		wg.Wait()
		fmt.Printf("All 3 inner products verified successfully \n")

		
	}else{
		
		lhs_g_pow_l_of_x := genPowerVec(pp, vec_g, l_x)
		lhs_b_star_pow_r_of_x := genPowerVec(pp, vec_b_star, r_x)
		lhs_2 := new(big.Int).Mul(lhs_h_pow_mew_b, lhs_g_pow_l_of_x)
		lhs_2.Mod(lhs_2, p)
		lhs_2.Mul(lhs_2, lhs_b_star_pow_r_of_x)
		lhs_2.Mod(lhs_2, p)
		if lhs_2.Cmp(rhs_2) != 0 {
			fmt.Printf("verification 2 of step 11 failed \n")
			os.Exit(-1)
		}

		// (v)   h^{mew_c} * (vec_g)^{l(x)} * (c*)^r =? A_L * A{R,c}^x * S_L^{x^2} * S_{R,c}^{x^3} * (vec_g)^{z^3*vec_y^-n} * (c*)^{-x*vec_y_z}
		lhs_h_pow_mew_c := new(big.Int).Exp(h, mew_c, p)
		lhs_c_star_pow_r_of_x := genPowerVec(pp, vec_c_star, r_x)
		lhs_3 := new(big.Int).Mul(lhs_h_pow_mew_c, lhs_g_pow_l_of_x)
		lhs_3.Mod(lhs_3, p)
		lhs_3.Mul(lhs_3, lhs_c_star_pow_r_of_x)
		lhs_3.Mod(lhs_3, p)

		if lhs_3.Cmp(rhs_3) != 0 {
			fmt.Printf("verification 3 of step 11 failed \n")
			os.Exit(-1)
		}	

		// (vi) t =? <l,r>
		inner_prod_result := innerProduct(pp, l_x, r_x)
		if inner_prod_result.Cmp(t_x) != 0 {
			fmt.Printf("verification 4 (inner product) of step 11 failed \n")
			os.Exit(-1)
		}
	}

	fmt.Printf("Shuffle argument by player %v verified successfully by all other players (using inner product argument = %v)\n", prover.Id, with_inner_product)
	
	
}	