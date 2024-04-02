package player

import (
	"crypto/sha256"
	"fmt"
	"main/preprocessing"
	"math/big"
)

type Proof struct{
	U []*big.Int
	V []*big.Int
	C [32]byte
	Z []*big.Int
} 

// given vec_h := {g^{r_i}}, prove knowledge of r_i's, secret_x := r (using AND Protocol + Fiat Shamir)
func (prover *Player) SchnorrProofFS(pp preprocessing.PublicParameters, sliceH, secretsX []*big.Int) Proof{
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	g := pp.GetGeneratorG()
	// Prover generates a random value r and published g^r
	sliceRTmp := prover.GenerateNRandVals(pp, len(sliceH))
	sliceU := []*big.Int{}
	u := new(big.Int)
	for _, rTmp := range sliceRTmp{
		u = new(big.Int).Exp(g, rTmp, p)
		sliceU = append(sliceU, u)
		}
	// Using Fiat-Shamir: hash function 
	c := sha256.Sum256([]byte(fmt.Sprintf("%v%v", sliceU, sliceH)))
	// z = r + (secret_val)* c
	z_tmp := new(big.Int).SetBytes(c[:])
	z_tmp.Mod(z_tmp, q)
	sliceZ := []*big.Int{}
	for idx, x_i := range secretsX {
		z_i := new(big.Int).Mul(z_tmp, x_i)
		z_i.Mod(z_i, q)
		z_i.Add(sliceRTmp[idx], z_i)
		z_i.Mod(z_i, q)
		sliceZ = append(sliceZ, z_i)
	}
	generated_proof := Proof{
		U: sliceU,
		C: c,
		Z: sliceZ,
	}
	return generated_proof
}
/* Verification: Proof is pi = (u:= g^r_tmp, c, z := r_tmp + r*c)  h := g^r
			V checks if c = H(g,u, h) 
			V checks if g^z = u * h^c*/
func (player *Player) VerifySchnorrProof(pp preprocessing.PublicParameters, sliceH []*big.Int, proof Proof) bool{
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	g := pp.GetGeneratorG()
	c_prime := sha256.Sum256([]byte(fmt.Sprintf("%v%v", proof.U, sliceH)))
	if c_prime != proof.C{
		fmt.Printf("The two hashes (%v) (Sch) (%v) do not match \n", c_prime, proof.C)
		return false
	} 
	for idx := range proof.Z {
		g_prime_i := new(big.Int).Exp(g, proof.Z[idx], p)
		c_tmp := new(big.Int).SetBytes(proof.C[:])
		c_tmp.Mod(c_tmp, q)

		rhs_product_tmp_g_i := new(big.Int).Exp(sliceH[idx], c_tmp, p)
		rhs_product_g_i := new(big.Int).Mul(proof.U[idx], rhs_product_tmp_g_i )
		rhs_product_g_i.Mod(rhs_product_g_i, p)

		if g_prime_i.Cmp(rhs_product_g_i) != 0 {
			fmt.Println("The verification for g does not work!")
			return false
		}
	}
	return true
}



// Given g, h, a:= g^w, b:= h^w, w: prover demonstrates that the same exponent w has been used for both a and b (Using AND Protocol + Fiat-Shamir)
func (prover *Player) DHTupleProofFS(pp preprocessing.PublicParameters, h *big.Int, a, b, w []*big.Int) Proof{
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	g := pp.GetGeneratorG()
	sliceRTmp := prover.GenerateNRandVals(pp, len(a))
	sliceU := []*big.Int{}
	sliceV := []*big.Int{}
	u := new(big.Int)
	v := new(big.Int)
	for _, rTmp := range sliceRTmp{
		u = new(big.Int).Exp(g, rTmp, p)
		v = new(big.Int).Exp(h, rTmp, p)
		sliceU = append(sliceU, u)
		sliceV = append(sliceV, v)
	}
	c := sha256.Sum256([]byte(fmt.Sprintf("%v%v%v%v", sliceU, a, sliceV, b)))
	z_tmp := new(big.Int).SetBytes(c[:])
	z_tmp.Mod(z_tmp, q)
	// z = r + w * c
	sliceZ := []*big.Int{}
	for idx, w_i := range w {
		z_i := new(big.Int).Mul(z_tmp, w_i)
		z_i.Mod(z_i, q)
		z_i.Add(sliceRTmp[idx], z_i)
		z_i.Mod(z_i, q)
		sliceZ = append(sliceZ, z_i)
	}
	generated_proof := Proof{
		U: sliceU,
		V: sliceV,
		C: c,
		Z: sliceZ,
	}

	return generated_proof
}

/* Verification: Proof is pi = (u, v, c, z)
		V checks if c = H(g, u, a, v, b) 
		V checks  Check if g^z == u * a^c and h^z == v * b^c
*/
func (player *Player) VerifyDHProof(pp preprocessing.PublicParameters, h *big.Int, a, b []*big.Int, proof Proof) bool{
	p := pp.GetPrimeP()
	q := pp.GetPrimeQ()
	g := pp.GetGeneratorG()
	c_prime := sha256.Sum256([]byte(fmt.Sprintf("%v%v%v%v", proof.U, a, proof.V, b)))
	if c_prime != proof.C{
		fmt.Println("The two hashes (DH) do not match")
		return false
	}
	// Check if g^z == u * a^c and h^z == v * b^c
	for idx := range proof.Z {
		g_prime_i := new(big.Int).Exp(g, proof.Z[idx], p)
		c_tmp := new(big.Int).SetBytes(proof.C[:])
		c_tmp.Mod(c_tmp, q)
		rhs_product_tmp_g_i := new(big.Int).Exp(a[idx], c_tmp, p)
		rhs_product_g_i := new(big.Int).Mul(proof.U[idx], rhs_product_tmp_g_i )
		rhs_product_g_i.Mod(rhs_product_g_i, p)
		h_prime_i := new(big.Int).Exp(h, proof.Z[idx], p)
		rhs_product_tmp_h_i := new(big.Int).Exp(b[idx], c_tmp, p)
		rhs_product_h_i := new(big.Int).Mul(proof.V[idx], rhs_product_tmp_h_i )
		rhs_product_h_i.Mod(rhs_product_h_i, p)
		if g_prime_i.Cmp(rhs_product_g_i) != 0 {
			fmt.Println("The verification for g does not work!")
			return false
		}
		if h_prime_i.Cmp(rhs_product_h_i) != 0 {
			fmt.Println("The verification for h does not work!")
			return false
		}
	}
	return true
}