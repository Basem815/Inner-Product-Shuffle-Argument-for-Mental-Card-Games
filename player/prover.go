package player

import (
	"fmt"
	"main/preprocessing"
	"math/big"
	"os"
)

type Prover struct {
	Player
	
	Secret_permutation []int    		// Used during the shuffle
	Sigma_v            *big.Int 		// Used for the power argument
	Sigma_w            *big.Int 		// Used for the power argument
	a_l []*big.Int						// Generated from Step4A
	a_r []*big.Int						// Generated from Step4A
	alpha, beta, rho_b, rho_c *big.Int	// Generated from Step4B
	s_l []*big.Int						// Generated from Step4B
	s_r []*big.Int						// Generated from Step4B
	l_0, l_2, r_1, r_3 []*big.Int		// Generated from Step 8
	tau_1, tau_3, tau_5 *big.Int		// Generated from Step 8
	t_1_x, t_3_x, t_5_x *big.Int		// Innerproducts (<l_0, r_1>, (<l_0, r_3> + <l_2, r_1> ), <l_2, r_3>) respectively
	t_1 *big.Int
	l_x, r_x []*big.Int

	// Power argument
	a_rPow, a_lPow []*big.Int
	alphaPow, betaPow *big.Int
	s_lPow, s_rPow []*big.Int

	l_w_0, l_w_1, r_w_0, r_w_1 []*big.Int		// Generated from Step 8Pow
	tau_w_0, tau_w_1, tau_w_2 *big.Int			// Generated from Step 8
	t_w_x_0, t_w_x_1, t_w_x_2 *big.Int
	t_w_0 *big.Int

	l_w_x, r_w_x []*big.Int
}


// l(X) = a_l + z^3y^{-n} + s_l * X^2
func lOfX(pp preprocessing.PublicParameters, a_l, zy, s_l []*big.Int, x *big.Int) []*big.Int{
	if len(a_l) != len(zy) && len(a_l) != len(s_l) {
		fmt.Printf("Lengths of the vectors should match!")
		os.Exit(-1)
	}
	tempResult := addTwoSlices(pp, a_l, zy)
	x_2 := new(big.Int).Mul(x, x)
	s_l_times_x_2 := multiplySliceByScalar(pp, s_l, x_2)
	l_of_x := addTwoSlices(pp, tempResult, s_l_times_x_2 )
	return l_of_x
}

// r(X) = y^{n} o (a_rX + s_rX^3) -  y_{z}^{n-2}
func rOfX(pp preprocessing.PublicParameters, a_r, y_n, y_z, s_r []*big.Int, x *big.Int) []*big.Int{
	if len(a_r) != len(y_n) && len(a_r) != len(y_z) && len(a_r) != len(s_r) {
		fmt.Printf("Lengths of the vectors should match!")
		os.Exit(-1)
	}
	a_r_times_x := multiplySliceByScalar(pp, a_r, x)
	x_3 := new(big.Int).Mul(x, x)
	x_3.Mod(x_3, pp.GetPrimeQ())
	x_3.Mul(x_3, x)
	x_3.Mod(x_3, pp.GetPrimeQ())
	s_r_times_x_3 := multiplySliceByScalar(pp, s_r, x_3)
	tempResult := addTwoSlices(pp, a_r_times_x, s_r_times_x_3)
	tempResult2 := MultiplyTwoSlices(pp, tempResult, y_n)
	y_z_times_x := multiplySliceByScalar(pp, y_z, x)
	r_of_x := subTwoSlices(pp, tempResult2, y_z_times_x)
	return r_of_x
}


func isGenerator(pp preprocessing.PublicParameters, gen *big.Int) bool{
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	return new(big.Int).Exp(gen, q, p).Cmp(big.NewInt(1)) == 0  
}

/* if the CRS satisfies the following conditions: G is a group of prime order, g \elt G
		and g != 1 for all group elements g in the CRS then
			Accept;
		else
			Reject;
	end*/
func (prover Prover) CRSCheck(pp preprocessing.PublicParameters) {
	
	p := pp.GetPrimeP()
	g := pp.GetGeneratorG()
	h := pp.GetGeneratorH()
	vec_g := pp.GetGeneratorsVec_G()
	if !p.ProbablyPrime(20) {
		fmt.Println("p is not a valid prime number")
		os.Exit(-1)
	}
	if !isGenerator(pp, g) || g.Cmp(big.NewInt(1)) == 0 {
		fmt.Println("g is not a valid generator")
		os.Exit(-1)
	}
	if !isGenerator(pp, h) || h.Cmp(big.NewInt(1)) == 0 {
		fmt.Println("h is not a valid generator")
		os.Exit(-1)
	}
	for idx ,elt := range vec_g {
		if !isGenerator(pp, elt) || elt.Cmp(big.NewInt(1)) == 0 {
			fmt.Printf("%v at position %v s not a valid generator", elt, idx)
			os.Exit(-1)
		}
	} 
}

func (prover *Prover) Step4A(pp preprocessing.PublicParameters, k []*big.Int) (){
	q := pp.GetPrimeQ()
	permutation_used := prover.Secret_permutation
	permutation_inverse := make([]int, len(permutation_used))
	for i, val := range permutation_used{
		permutation_inverse[val-1] = i+1
	}
	secret_s := prover.Secret_s
	a_r := []*big.Int{}							//  a_r = (s*k_{pi^{-1}(1)}, ...,  s*k_{pi^{-1}(n)})
	for _, val := range permutation_inverse{
		prod :=  new(big.Int).Mul(secret_s, k[val-1])
		prod.Mod(prod, q)
		a_r = append(a_r, prod)
	}
	// (ii)	Compute a_l = (1, s*k_{pi^{-1}(1)}, s^{2}*k_{pi^{-1}(1)}*k_{pi^{-1}(2)},  ...,  s^{n-1}*k_{pi^{-1}(1)}*...*k_{pi^{-1}(n-1)})
	a_l := []*big.Int{}
	a_l = append(a_l, big.NewInt(1))
	for i, val := range permutation_inverse{
		if i == len(permutation_inverse) - 1 {
			break
		}
		prod := new(big.Int).Set(secret_s)      // Set it to s each iteration 
		prod.Mul(prod, a_l[i])					// Multiply with previous value of a_l
		prod.Mod(prod, q)
		prod.Mul(prod, k[val-1])				// Multiply with k[pi^{-1}[i]]
		prod.Mod(prod, q)
		a_l = append(a_l, prod)
	}
	prover.a_l = a_l
	prover.a_r = a_r
}


// Generate random values
func (prover *Prover) Step4B(pp preprocessing.PublicParameters, n int) (){
	alpha, beta := prover.GenerateRandValue(pp), prover.GenerateRandValue(pp)
	rho_b, rho_c := prover.GenerateRandValue(pp), prover.GenerateRandValue(pp)
	s_l, s_r := make([]*big.Int, n), make([]*big.Int, n)
	for i := 0; i < n; i++ {
		s_l[i], s_r[i] = prover.GenerateRandValue(pp), prover.GenerateRandValue(pp)		
	}
	prover.alpha = alpha		
	prover.beta = beta
	prover.rho_b = rho_b
	prover.rho_c = rho_c
	prover.s_l = s_l
	prover.s_r = s_r
}

// For power argument
func (prover *Prover) Step4Power(pp preprocessing.PublicParameters, n int) (){

	a_rPow := []*big.Int{}
	a_rPow = append(a_rPow, prover.Secret_s)
	a_lPow := []*big.Int{}
	a_lPow = append(a_lPow, big.NewInt(1))
	for i:= 1; i <n; i++ {
		a_rPow = append(a_rPow, prover.Secret_s)
		a_lPowVal := new(big.Int).Mul(prover.Secret_s, a_lPow[i-1])
		a_lPowVal.Mod(a_lPowVal, pp.GetPrimeQ())
		a_lPow = append(a_lPow, a_lPowVal)
	}

	alphaPow, betaPow := prover.GenerateRandValue(pp), prover.GenerateRandValue(pp)
	// (iv)
	s_lPow, s_rPow := make([]*big.Int, n), make([]*big.Int, n)
	for i := 0; i < n; i++ {
		s_lPow[i], s_rPow[i] = prover.GenerateRandValue(pp), prover.GenerateRandValue(pp)		
	}

	prover.a_rPow = a_rPow
	prover.a_lPow = a_lPow
	prover.alphaPow = alphaPow		
	prover.betaPow = betaPow
	prover.s_lPow = s_lPow
	prover.s_rPow = s_rPow
}


func (prover *Prover) Step5 (pp preprocessing.PublicParameters, vec_b, vec_c []*big.Int) (A_L, S_L, S_rb, S_rc *big.Int) {
	p := pp.GetPrimeP()
	vec_g := pp.GetGeneratorsVec_G()
	h := pp.GetGeneratorH()
	A_L = genPowerVec(pp, vec_g, prover.a_l)
	h_pow_alph :=  new(big.Int).Exp(h, prover.alpha , p )
	A_L.Mul(A_L, h_pow_alph)
	A_L.Mod(A_L, p)
	S_L = genPowerVec(pp, vec_g, prover.s_l)
	h_pow_beta :=  new(big.Int).Exp(h, prover.beta, p )
	S_L.Mul(S_L, h_pow_beta)
	S_L.Mod(S_L, p)
	S_rb = genPowerVec(pp, vec_b, prover.s_r)
	h_pow_rho_b :=  new(big.Int).Exp(h, prover.rho_b, p )
	S_rb.Mul(S_rb, h_pow_rho_b)
	S_rb.Mod(S_rb, p)
	S_rc = genPowerVec(pp, vec_c, prover.s_r)
	h_pow_rho_c :=  new(big.Int).Exp(h, prover.rho_c, p )
	S_rc.Mul(S_rc, h_pow_rho_c)
	S_rc.Mod(S_rc, p)
	return A_L, S_L, S_rb, S_rc
}

// For power argument
func (prover *Prover) Step5Power (pp preprocessing.PublicParameters) (A_W, S_W *big.Int) {
	p := pp.GetPrimeP()
	vec_g := pp.GetGeneratorsVec_G()
	vec_h := pp.GetGeneratorsVec_H()
	h := pp.GetGeneratorH()

	A_W = genPowerVec(pp, vec_g, prover.a_lPow)
	A_W_tmp := genPowerVec(pp, vec_h, prover.a_rPow)
	A_W.Mul(A_W, A_W_tmp)
	A_W.Mod(A_W, p)
	h_pow_alph :=  new(big.Int).Exp(h, prover.alphaPow , p )

	A_W.Mul(A_W, h_pow_alph)
	A_W.Mod(A_W, p)

	S_W = genPowerVec(pp, vec_g, prover.s_lPow)
	S_W_tmp := genPowerVec(pp, vec_h, prover.s_rPow)
	S_W.Mul(S_W, S_W_tmp)
	S_W.Mod(S_W, p)
	h_pow_beta :=  new(big.Int).Exp(h, prover.betaPow , p )

	S_W.Mul(S_W, h_pow_beta)
	S_W.Mod(S_W, p)

	return A_W, S_W
}

func (prover *Prover) Step8 (pp preprocessing.PublicParameters, vec_y, vec_y_z, vec_z3_times_yn []*big.Int,
	k_sum, k_prod, delta_y_z *big.Int, n int) (*big.Int, *big.Int){
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	secret_s := prover.Secret_s
	h := pp.GetGeneratorH()
	g := pp.GetGeneratorG()
	// (i) 
	y := vec_y[1]
	z := vec_y_z[0]
	z_3 := new(big.Int).Exp(z, big.NewInt(3), q)
	l_0 := addTwoSlices(pp, prover.a_l, vec_z3_times_yn)		// a_l + z^3y^{-n}
	l_2 := make([]*big.Int, len(prover.s_l))
	copy(l_2, prover.s_l)
	r_1_tmp := MultiplyTwoSlices(pp, prover.a_r, vec_y)		// (a_r o y^n) 
	r_1 := subTwoSlices(pp, r_1_tmp, vec_y_z)			// (a_r o y^n) - y_z^{n-2}
	r_3 := MultiplyTwoSlices(pp, prover.s_r, vec_y)			// s_r o y^n
	t_x_1 := innerProduct(pp, l_0, r_1)
	t_x_3a := innerProduct(pp, l_0, r_3)
	t_x_3b := innerProduct(pp, l_2, r_1)
	t_x_3 := new(big.Int).Add(t_x_3a, t_x_3b)
	t_x_3.Mod(t_x_3, q)
	t_x_5 := innerProduct(pp, l_2, r_3)

	// (iv):  t_1 = (s^n)*(k^)*y^{n-1} + s*z^3*(k*) - delta(y,z) 	
	t_1_tmp_1 := new(big.Int).Exp(secret_s,  big.NewInt(int64(n)), q)
	t_1_tmp_1.Mul(t_1_tmp_1, k_prod)
	t_1_tmp_1.Mod(t_1_tmp_1, q)
	y_pow_n_min_1 := new(big.Int).Exp(y, big.NewInt(int64(n-1)), q)
	t_1_tmp_1.Mul(t_1_tmp_1, y_pow_n_min_1)
	t_1_tmp_1.Mod(t_1_tmp_1, q)
	t_1_tmp_2 := new(big.Int).Mul(secret_s, z_3)
	t_1_tmp_2.Mod(t_1_tmp_2, q)
	t_1_tmp_2.Mul(t_1_tmp_2, k_sum) 
	t_1_tmp_2.Mod(t_1_tmp_2, q)
	t_1_tmp_2.Sub(t_1_tmp_2, delta_y_z)		// Changed this to subtract
	t_1_tmp_2.Mod(t_1_tmp_2, q)
	t_1 := new(big.Int).Add(t_1_tmp_1, t_1_tmp_2)
	t_1.Mod(t_1, q)							
	prover.t_1 = t_1

	// (v)   tau_i <-- Z_p*  i = {3,5}
	tau_3, tau_5 := prover.GenerateRandValue(pp), prover.GenerateRandValue(pp)

	// (vi)  T_i = g^{t_i}*h^{tau_i}  i = {3,5}
	T_3 := new(big.Int).Exp(g, t_x_3, p)
	T_3.Mul(T_3, new(big.Int).Exp(h, tau_3, p) )
	T_3.Mod(T_3, p)						
	T_5 := new(big.Int).Exp(g, t_x_5, p)
	T_5.Mul(T_5, new(big.Int).Exp(h, tau_5, p) )
	T_5.Mod(T_5, p)	

	// (vii) : tau_1 := (sigma_v)*(z^3)*(k_sum) + (sigma_w)*(y^{n-1})*k_prod 
	tau_1_tmp_1 := new(big.Int).Mul(prover.Sigma_v, z_3)
	tau_1_tmp_1.Mod(tau_1_tmp_1, q)
	tau_1_tmp_1.Mul(tau_1_tmp_1, k_sum)
	tau_1_tmp_1.Mod(tau_1_tmp_1, q)
	tau_1_tmp_2 := new(big.Int).Mul(prover.Sigma_w, new(big.Int).Exp(y, big.NewInt(int64(n-1)), q))
	tau_1_tmp_2.Mod(tau_1_tmp_2, q)
	tau_1_tmp_2.Mul(tau_1_tmp_2, k_prod)
	tau_1_tmp_2.Mod(tau_1_tmp_2, q)
	tau_1 := new(big.Int).Add(tau_1_tmp_1, tau_1_tmp_2)
	tau_1.Mod(tau_1, q)

	prover.l_0, prover.l_2, prover.r_1 , prover.r_3   = l_0, l_2, r_1, r_3
	prover.tau_1 = tau_1
	prover.tau_3, prover.tau_5 = tau_3, tau_5
	prover.t_1_x, prover.t_3_x, prover.t_5_x = t_x_1, t_x_3, t_x_5
	return T_3, T_5 
}


func (prover *Prover) Step8Power (pp preprocessing.PublicParameters, vec_y, vec_y_inverse, vec_y_z, vec_w, vec_w_0 []*big.Int,
	delta_w_y_z *big.Int, n int) (*big.Int, *big.Int){
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	secret_s := prover.Secret_s
	h := pp.GetGeneratorH()
	g := pp.GetGeneratorG()

	// (i) 
	w := vec_w[1]
	y := vec_y[1]
	z := vec_y_z[0]
	z_times_vec_y_inverse := multiplySliceByScalar(pp, vec_y_inverse, z)
	l_w_0_tmp1 := addTwoSlices(pp, prover.a_lPow, z_times_vec_y_inverse)

	vec_w_0_times_y_inverse := multiplySliceByScalar(pp, vec_w_0, vec_y_inverse[1])

	l_w_0_tmp2 := subTwoSlices(pp, vec_w, vec_w_0_times_y_inverse)

	l_w_0 := addTwoSlices(pp, l_w_0_tmp1, l_w_0_tmp2)
	l_w_1 := make([]*big.Int, len(prover.s_lPow))
	copy(l_w_1, prover.s_lPow)
	
	r_w_tmp0 := MultiplyTwoSlices(pp, vec_y, prover.a_rPow)
	r_w_0 := subTwoSlices(pp, r_w_tmp0, vec_y_z)
	r_w_1 := MultiplyTwoSlices(pp, vec_y, prover.s_rPow)
	
	prover.l_w_0, prover.l_w_1, prover.r_w_0, prover.r_w_1 = l_w_0, l_w_1, r_w_0, r_w_1
	
	t_w_x_0 := innerProduct(pp, l_w_0, r_w_0)

	t_w_x_1a := innerProduct(pp, l_w_1, r_w_0)
	t_w_x_1b := innerProduct(pp, l_w_0, r_w_1)
	t_w_x_1 := new(big.Int).Add(t_w_x_1a, t_w_x_1b)
	t_w_x_1.Mod(t_w_x_1, q)
	t_w_x_2 := innerProduct(pp, l_w_1, r_w_1)		// Correct value

	
	// (iv): t_{0,w} = s^{n}y^{n-1} + s( (wy)^{n-1} + nz) + delta(w,y,z)
	s_pow_n := new(big.Int).Exp(secret_s, big.NewInt(int64(n)), q)
	y_pow_n_min_1 := new(big.Int).Exp(y, big.NewInt(int64(n-1)), q)

	t_0_w_tmp_1 := new(big.Int).Mul(s_pow_n, y_pow_n_min_1)
	t_0_w_tmp_1.Mod(t_0_w_tmp_1, q)				// s^{n}y^{n-1}

	w_times_y := new(big.Int).Mul(w, y)
	w_times_y.Mod(w_times_y, q)
	w_times_y_pow_n_min_1 := new(big.Int).Exp(w_times_y, big.NewInt(int64(n-1)), q)
	n_times_z := new(big.Int).Mul(z, big.NewInt(int64(n)))
	n_times_z.Mod(n_times_z, q)

	n_times_z_plus_prev := new(big.Int).Add(w_times_y_pow_n_min_1, n_times_z)
	n_times_z_plus_prev.Mod(n_times_z_plus_prev, q)				// (wy)^{n-1} + nz

	t_0_w_tmp_2 := new(big.Int).Mul(n_times_z_plus_prev, secret_s)
	t_0_w_tmp_2.Mod(t_0_w_tmp_2, q)				// s( (wy)^{n-1} + nz)
	
	t_0_w := new(big.Int).Add(t_0_w_tmp_1, t_0_w_tmp_2)
	t_0_w.Mod(t_0_w, q)
	
	t_0_w.Add(t_0_w, delta_w_y_z)
	t_0_w.Mod(t_0_w, q)

	prover.t_w_0 = t_0_w
	
	// (v)   tau_w_i <-- Z_p*  i = {1,2}
	tau_w_1, tau_w_2 := prover.GenerateRandValue(pp), prover.GenerateRandValue(pp)
	
	// (vi)  T_i = g^{t_w_i}*h^{tau_i}  i = {1,2}
	T_w_1 := new(big.Int).Exp(g, t_w_x_1, p)
	T_w_1.Mul(T_w_1, new(big.Int).Exp(h, tau_w_1, p) )
	T_w_1.Mod(T_w_1, p)		

	T_w_2 := new(big.Int).Exp(g, t_w_x_2, p)
	T_w_2.Mul(T_w_2, new(big.Int).Exp(h, tau_w_2, p) )
	T_w_2.Mod(T_w_2, p)		
		
	

	// tau_w_0 := (sigma_v) * ( (wy)^{n-1} + nz) + (sigma_w)y^{n-1}
	tau_w_0_tmp_1 := new(big.Int).Mul(prover.Sigma_v, n_times_z_plus_prev)
	tau_w_0_tmp_1.Mod(tau_w_0_tmp_1, q)
	tau_w_0_tmp_2 := new(big.Int).Mul(prover.Sigma_w, y_pow_n_min_1)
	tau_w_0_tmp_2.Mod(tau_w_0_tmp_2, q)

	tau_w_0 := new(big.Int).Add(tau_w_0_tmp_1, tau_w_0_tmp_2)
	tau_w_0.Mod(tau_w_0, q)
	
	
	prover.tau_w_0 = tau_w_0
	prover.tau_w_1, prover.tau_w_2 = tau_w_1, tau_w_2
	prover.t_w_x_0, prover.t_w_x_1, prover.t_w_x_2 = t_w_x_0, t_w_x_1, t_w_x_2
	return T_w_1, T_w_2 
}

func (prover *Prover) Step10 (pp preprocessing.PublicParameters, vec_y, vec_y_z, vec_z3_times_yn []*big.Int, 
		x *big.Int, n int ) ( *big.Int,*big.Int,*big.Int,*big.Int){
	q := pp.GetPrimeQ()
	x_pow_2 := new(big.Int).Exp(x, big.NewInt(int64(2)), q)
	x_pow_3 := new(big.Int).Exp(x, big.NewInt(int64(3)), q)
	x_pow_5 := new(big.Int).Exp(x, big.NewInt(int64(5)), q)
	l_x := lOfX(pp, prover.a_l, vec_z3_times_yn, prover.s_l, x )
	r_x := rOfX(pp, prover.a_r, vec_y, vec_y_z, prover.s_r, x)
	prover.l_x = l_x
	prover.r_x = r_x
	/// (iii)
	t_x_1, t_x_3, t_x_5  := prover.t_1_x, prover.t_3_x, prover.t_5_x
	t_x_1.Mul(t_x_1, x)
	t_x_1.Mod(t_x_1, q)
	t_x_3.Mul(t_x_3, x_pow_3)
	t_x_3.Mod(t_x_3, q)
	t_x_5.Mul(t_x_5, x_pow_5)
	t_x_5.Mod(t_x_5, q)
	t_x_tmp := new(big.Int).Add(t_x_1, t_x_3)
	t_x_tmp.Mod(t_x_tmp, q)
	t_x := new(big.Int).Add(t_x_tmp, t_x_5)
	t_x.Mod(t_x, q)
	// (iv)
	tau_x := new(big.Int).Mul(prover.tau_1 ,x)
	tau_x.Mod(tau_x, q)
	tmp_prod := new(big.Int).Mul(prover.tau_3, x_pow_3)
	tmp_prod.Mod(tmp_prod, q)
	tau_x.Add(tau_x, tmp_prod)
	tau_x.Mod(tau_x, q)
	tmp_prod2 := new(big.Int).Mul(prover.tau_5, x_pow_5)
	tmp_prod2.Mod(tmp_prod2, q)
	tau_x.Add(tau_x, tmp_prod2)
	tau_x.Mod(tau_x, q)

	// (v)   mew_b = alpha + beta*(x^2) + rho_b*(x^3)
	tmp_mew_1 := new(big.Int).Mul(prover.beta, x_pow_2)
	tmp_mew_1.Mod(tmp_mew_1, q)
	tmp_mew_b := new(big.Int).Mul(prover.rho_b, x_pow_3)
	tmp_mew_b.Mod(tmp_mew_b, q)

	// (vi)  mew_c = alpha + beta*(x^2) + rho_c*(x^3)
	tmp_mew_c := new(big.Int).Mul(prover.rho_c, x_pow_3)
	tmp_mew_c.Mod(tmp_mew_c, q)
	mew_b := new(big.Int).Add(prover.alpha, tmp_mew_1)
	mew_b.Mod(mew_b, q)
	mew_b.Add(mew_b, tmp_mew_b)
	mew_b.Mod(mew_b, q)
	mew_c := new(big.Int).Add(prover.alpha, tmp_mew_1)
	mew_c.Mod(mew_c, q)
	mew_c.Add(mew_c, tmp_mew_c)
	mew_c.Mod(mew_c, q)
	return t_x, tau_x, mew_b, mew_c
}


func (prover *Prover) Step10Pow (pp preprocessing.PublicParameters, vec_y, vec_y_z, vec_z3_times_yn []*big.Int, 
		x *big.Int, n int ) ( *big.Int,*big.Int,*big.Int){
	q := pp.GetPrimeQ()
	x_pow_2 := new(big.Int).Exp(x, big.NewInt(int64(2)), q)

	l_w_x_tmp := multiplySliceByScalar(pp, prover.l_w_1, x)
	l_w_x := addTwoSlices(pp, prover.l_w_0, l_w_x_tmp)

	r_w_x_tmp := multiplySliceByScalar(pp, prover.r_w_1, x)
	r_w_x := addTwoSlices(pp, prover.r_w_0, r_w_x_tmp)

	prover.l_w_x = l_w_x
	prover.r_w_x = r_w_x
	
	/// (iii)
	t_w_x_0, t_w_x_1, t_w_x_2  := prover.t_w_x_0, prover.t_w_x_1, prover.t_w_x_2 	// Innerproducts
	t_w_x_1.Mul(t_w_x_1, x)
	t_w_x_1.Mod(t_w_x_1, q)
	t_w_x_2.Mul(t_w_x_2, x_pow_2)
	t_w_x_2.Mod(t_w_x_2, q)
	
	t_x_tmp := new(big.Int).Add(t_w_x_0, t_w_x_1)
	t_x_tmp.Mod(t_x_tmp, q)
	t_w_x := new(big.Int).Add(t_x_tmp, t_w_x_2)
	t_w_x.Mod(t_w_x, q)				// Should be equal to <l_w, r_w>

	// (iv)
	tau_w_x := new(big.Int).Mul(prover.tau_w_1 ,x)
	tau_w_x.Mod(tau_w_x, q)
	tau_w_2_times_x2 := new(big.Int).Mul(prover.tau_w_2, x_pow_2)
	tau_w_2_times_x2.Mod(tau_w_2_times_x2, q)
	tau_w_x.Add(tau_w_x, tau_w_2_times_x2)
	tau_w_x.Mod(tau_w_x, q)
	tau_w_x.Add(tau_w_x, prover.tau_w_0)
	tau_w_x.Mod(tau_w_x, q)

	// (v)   mew_w = alpha_w + beta_w*x
	tmp_mew_w_1 := new(big.Int).Mul(prover.betaPow, x)
	tmp_mew_w_1.Mod(tmp_mew_w_1, q)
	mew_w := new(big.Int).Add(prover.alphaPow, tmp_mew_w_1)
	mew_w.Mod(mew_w, q)


	return t_w_x, tau_w_x, mew_w
}


/* Returns commitments V and W where :
	- V = g^s * h^{sigma_v}
	- W = (g^s^{n}) * h^{sigma_w}*/

func (prover *Prover) PowerArgComs(pp preprocessing.PublicParameters, n int ) (*big.Int, *big.Int){
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	g := pp.GetGeneratorG()
	h := pp.GetGeneratorH()
	secret_s := prover.Secret_s
	s_pow_n := new(big.Int).Exp(secret_s,  big.NewInt(int64(n)), q)
	V := new(big.Int).Mul(new(big.Int).Exp(g, secret_s, p), new(big.Int).Exp(h, prover.Sigma_v, p) )
	V.Mod(V, p)
	W := new(big.Int).Mul(new(big.Int).Exp(g, s_pow_n, p), new(big.Int).Exp(h, prover.Sigma_w, p) )
	W.Mod(W, p)
	return V, W
}