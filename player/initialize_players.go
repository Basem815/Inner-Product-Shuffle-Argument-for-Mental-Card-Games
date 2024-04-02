package player

import (
	"crypto/rand"
	"fmt"
	"main/preprocessing"
	"math/big"
)


var nextId int = 1
func generateKey(pp preprocessing.PublicParameters) (sk, pk *big.Int) {
	x, _ := rand.Int(rand.Reader, new(big.Int).Sub(pp.GetPrimeQ(), big.NewInt(1))) 
	x.Add(x, big.NewInt(1))
	pub_key := new(big.Int).Exp(pp.GetGeneratorG(), x, pp.GetPrimeP())
	return x, pub_key
}

func createPlayer(pp preprocessing.PublicParameters) Player{
	sk, pk := generateKey(pp)
	newPlayer := Player{
		Id: nextId,
		secretKey: sk,
		PublicKey: pk,
	}
	sliceH := []*big.Int{}
	sliceH = append(sliceH, pk)
	secretsX := []*big.Int{}
	secretsX = append(secretsX, sk)
	newPlayer.KeyPair = newPlayer.SchnorrProofFS(pp, sliceH, secretsX)
	nextId++
	return newPlayer
}

func InitializePlayers(pp preprocessing.PublicParameters, numbOfPlayers int) []Player{
	playerSlice := []Player{}
	for i := 0; i < numbOfPlayers; i++ {
		playerSlice = append(playerSlice, createPlayer(pp))
	}
	verifiyKeyPairProof(pp, playerSlice)
	return playerSlice
}

// Should take a list of players along with a particular id and return the list without that player
func ExcludePlayer(allPlayers []Player, particularPlayerID int) []Player {
	otherPlayers := []Player{}
	for _, player := range allPlayers{
		if player.Id != particularPlayerID {
			otherPlayers = append(otherPlayers, player)
		}
	}
	return otherPlayers
}

func verifiyKeyPairProof(pp preprocessing.PublicParameters, players []Player) {
	for _, prover := range players {
		otherPlayers := ExcludePlayer(players, prover.Id)
		sliceH := []*big.Int{}
		sliceH = append(sliceH, prover.PublicKey)
		for _, verifier := range otherPlayers{
			if !verifier.VerifySchnorrProof(pp, sliceH, prover.KeyPair ) {
				panic ("Key-Pair does not match!")
			}
		}
	}
	fmt.Printf("Key-pairs of all %v players verified \n", len(players))
}