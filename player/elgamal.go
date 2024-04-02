package player

import (
	"crypto/rand"
	"fmt"
	"main/cards"
	"main/preprocessing"
	"math/big"
	"time"
)

// Input: (g^{x_1}, g^{x_2}, ... , g^{x_n})
// Output: g^{x_1+x_2+...+x_n}
func AggregatedPublicKey(pp preprocessing.PublicParameters, pub_keys []*big.Int) (*big.Int) {
	aggKey := big.NewInt(1)
	for _, key := range pub_keys {
		aggKey.Mul(aggKey, key)
		aggKey.Mod(aggKey, pp.GetPrimeP())
	}
	return aggKey
}

// Generates n random values r_i (for tuple (g^{r_i}, h^{r_i}) )
// Used to create initial ciphertexts
func (player *Player) GenerateRandomExponents(pp preprocessing.PublicParameters, pub_key *big.Int, n int) (a, b []*big.Int, c,d Proof){
	p := pp.GetPrimeP()
	g := pp.GetGeneratorG()
	q := pp.GetPrimeQ()
	secrets_r := []*big.Int{}
	exponentsG := []*big.Int{}
	exponentsH := []*big.Int{}
	outer:
	for len(exponentsG) < n {
		r, _ := rand.Int(rand.Reader, new(big.Int).Sub(q, big.NewInt(1))) 
		r.Add(r, big.NewInt(1))
		for _, vals := range exponentsG{
            // If the exponent has already been accounted for, skip
            if vals.Cmp(r) == 0 {
                continue outer
            }
        }
		for _, vals := range exponentsH{
            // If the exponent has already been accounted for, skip
            if vals.Cmp(r) == 0 {
                continue outer
            }
        }
		g_power_r := new(big.Int).Exp(g, r, p)
		h_power_r := new(big.Int).Exp(pub_key, r, p)
		secrets_r = append(secrets_r, r)
		exponentsG = append(exponentsG, g_power_r)
		exponentsH = append(exponentsH, h_power_r)
	}
	proofSchnorr := player.SchnorrProofFS(pp, exponentsG, secrets_r)
	proofDH := player.DHTupleProofFS(pp, pub_key, exponentsG, exponentsH, secrets_r)
	return exponentsG, exponentsH, proofSchnorr, proofDH
}

// Standard ElGamal encryption (g^{r_i}, h^{r_i}*msg) where msg := g^{m_i}
func encrypt(pp preprocessing.PublicParameters, agg_pub_key, msg, r_i *big.Int) (cipherText [2]*big.Int) {
	p := pp.GetPrimeP()
	g := pp.GetGeneratorG()
	c1 := new(big.Int).Exp(g, r_i, p)
	c2 := new(big.Int).Exp(agg_pub_key, r_i, p)
	c2.Mul(c2, msg)
	c2.Mod(c2, p)
	result := [2]*big.Int{
		c1,
		c2,
	}
	return result 
}

// Should return [(g^1, h^1*g^{m_1}), ...]
func openCiphertexts(pp preprocessing.PublicParameters, agg_key *big.Int, orgCards map[cards.Card]*big.Int) [][2]*big.Int {
	open_ciph_txt := [][2]*big.Int{}
	for _, groupVal := range orgCards{
		open_ciph_txt = append(open_ciph_txt, encrypt(pp, agg_key, groupVal, big.NewInt(1)))
	}
	return open_ciph_txt
}
// Should return [(g^{1+\bar(r_i)}, h^{\bar(r_i)}*g^{m_i}, .... ] 
func InitialCiphertexts(pp preprocessing.PublicParameters, agg_key *big.Int, players []Player, orgCards map[cards.Card]*big.Int) [][2]*big.Int{
	timeInitializeCiphertexts := time.Now()
	p := pp.GetPrimeP()
	ciphertexts := openCiphertexts(pp, agg_key, orgCards)
	for i, player := range players {
		g_pow_r, h_pow_r, proof_sch, proof_dh := player.GenerateRandomExponents(pp, agg_key, len(ciphertexts))	
		// Have every other player verify the proofs
		for j := range players {
			// skip player i
			if j == i{
				continue
			}else{
				if !players[j].VerifySchnorrProof(pp, g_pow_r, proof_sch) || 
					!players[j].VerifyDHProof(pp, agg_key, g_pow_r, h_pow_r, proof_dh){
					panic("Verification failed")
				}
			}
		}
		// If all proofs have been verified, append them to ciphertexts
		for idx := range ciphertexts{
			ciphertexts[idx][0].Mul(ciphertexts[idx][0], g_pow_r[idx])
			ciphertexts[idx][0].Mod(ciphertexts[idx][0], p)
			ciphertexts[idx][1].Mul(ciphertexts[idx][1], h_pow_r[idx])
			ciphertexts[idx][1].Mod(ciphertexts[idx][1], p)
		}
	}
	elapsed_time := time.Since(timeInitializeCiphertexts)
    fmt.Printf("Initializing ciphertexts function took %s\n", elapsed_time)
	return ciphertexts
}

// Using Bunz approach: Taking secret value to the exponent of the ciphertext (C' = (C)^s)
func ReEncrypt(pp preprocessing.PublicParameters, cipherText [2]*big.Int, secret_val *big.Int) (new_ciphertext [2]*big.Int){
	p := pp.GetPrimeP()
	new_c_0 := new(big.Int).Exp(cipherText[0], secret_val, p)
	new_c_1 := new(big.Int).Exp(cipherText[1], secret_val, p)
	return [2]*big.Int{
		new_c_0,
		new_c_1,
	}
}
// Removes secret key component
func (player *Player) PartialDecrypt(pp preprocessing.PublicParameters, cipherText [2]*big.Int) (*big.Int) {
	privKey := player.GetSecretKey()
	p := pp.GetPrimeP()
	expo := new(big.Int).Exp(cipherText[0], privKey, p )
	return new(big.Int).ModInverse(expo, p)
}

// Message decryption part
func (player *Player) PartialMessageDecrypt(pp preprocessing.PublicParameters, msg *big.Int) (*big.Int) {
	secretSInv := new(big.Int).ModInverse(player.Secret_s, pp.GetPrimeQ())
	p := pp.GetPrimeP()
	return new(big.Int).Exp(msg, secretSInv, p )
}

// The modified decryption function (Returns (g^{m_i}) instead of (g^{\bar{s}m_i}))
func (decrypter *Player) Decrypt(pp preprocessing.PublicParameters, cipherText [2]*big.Int,  allPlayers []Player) (*big.Int) {
	otherPlayers := ExcludePlayer(allPlayers, decrypter.Id)
	partial_decrypt := big.NewInt(1)
	// All other players partially decrypt the ciphertext
	for _,player := range otherPlayers{
		partial_decrypt.Mul(partial_decrypt,player.PartialDecrypt(pp, cipherText))
		partial_decrypt.Mod(partial_decrypt, pp.GetPrimeP())
	}	
	// Now decrypter can remove their component
	partial_decrypt.Mul(partial_decrypt, decrypter.PartialDecrypt(pp, cipherText))
	msg := new(big.Int).Mul(cipherText[1], partial_decrypt)
	msg.Mod(msg, pp.GetPrimeP())

	// Have decrypter generate a random temporary power and raise the message to that power
	ephemeralPowerDelta := decrypter.GenerateRandValue(pp)
	ephemeralPowerDeltaInverse := new(big.Int).ModInverse(ephemeralPowerDelta, pp.GetPrimeQ())

	newMsg := new(big.Int).Exp(msg, ephemeralPowerDelta, pp.GetPrimeP())
	// Have other players remove their secret randomizer s_j
	for _, player := range otherPlayers{
		newMsg = player.PartialMessageDecrypt(pp, newMsg)
	}
	// Now player gets rid of their own s as well as the epemeralPower
	newMsg = decrypter.PartialMessageDecrypt(pp, newMsg)
	newMsg.Exp(newMsg, ephemeralPowerDeltaInverse, pp.GetPrimeP())
	
	return newMsg
}

/* NOT used but left: The original decryption function (returns g^{s*m_i})
	Must call the following in main after this function returns: 	
		decryptedCard := cards.GroupEltToCard(pubParams, newDeck, decryptedMsg )
		fmt.Printf("Player %v decrypted card %v of the deck to obtain the value: %v \n", players[idx].Id , idx, decryptedCard )
*/
func (decrypter *Player) DecryptOrg(pp preprocessing.PublicParameters, cipherText [2]*big.Int, allPlayers []Player) (*big.Int) {
	otherPlayers := ExcludePlayer(allPlayers, decrypter.Id)
	partial_decrypt := big.NewInt(1)
	for _,player := range otherPlayers{
		partial_decrypt.Mul(partial_decrypt,player.PartialDecrypt(pp, cipherText))
		partial_decrypt.Mod(partial_decrypt, pp.GetPrimeP())
	}	
	// Now decrypter can remove their component
	partial_decrypt.Mul(partial_decrypt, decrypter.PartialDecrypt(pp, cipherText))
	msg := new(big.Int).Mul(cipherText[1], partial_decrypt)
	msg.Mod(msg, pp.GetPrimeP())
	return msg
}
