package main

import (
	"fmt"
	"main/cards"
	"main/player"
	"main/preprocessing"
	"math/big"
	"os"
	"syscall"
)



func main() {

	
	outputFile, err := os.OpenFile("output.txt", os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0666)
    if err != nil {
        fmt.Println("Error opening file:", err)
        return
    }
    defer outputFile.Close()

	// Redirect stdout to the file
    os.Stdout = outputFile


	useInnerProductArg := true
	numPlayers := 3
	numSuits := 4				// Assuming standard deck
	cardsPerSuit := 13		// A, 2, ... , J, Q, K, 14, 15, ...
	securityParam := 2048
	securityParamFixed := true		 //true: fixes 2048-bit values for p,q (otherwise take at least an hour to compute)
	numCards := numSuits*cardsPerSuit		
	fmt.Printf("Starting main with %v players, %v cards in total with security paramter of %v-bits \n", numPlayers, numCards, securityParam)
	pubParams := preprocessing.Setup(securityParam, numCards, securityParamFixed)	// Returns (p, q, generators)
	
	// Initializing the deck
	newDeck := cards.CreateDeck(numSuits, cardsPerSuit)				
	OrgCards := cards.CardsToGroupElts(pubParams, newDeck)			// Mapping from cards to group elements of the form g^{m_i)
	fmt.Println("Mapping for cards to group values created.")

	// Initializing players
	players := player.InitializePlayers(pubParams, numPlayers)
	pubKeys := []*big.Int{}
	for _, player := range players{
		pubKeys = append(pubKeys, player.PublicKey)
	}
	aggKey := player.AggregatedPublicKey(pubParams, pubKeys)
	fmt.Printf("%v Players initialized \n", len(players))


	ciphertexts := player.InitialCiphertexts(pubParams, aggKey, players, OrgCards)	// Original ciphertexts 	
	fmt.Println("Initial deck created")
	for idx := range players{
		prover, newGenG, shuffledCiphertext := players[idx].Shuffle(pubParams, ciphertexts)
		otherPlayers := player.ExcludePlayer(players, prover.Id)
		prover.IP(pubParams, otherPlayers, len(ciphertexts),  ciphertexts, shuffledCiphertext, useInnerProductArg)
		if idx%2 == 0{
			useInnerProductArg = false 
		}else{
			useInnerProductArg = true 
		}
		pubParams.SetGeneratorG(newGenG)
		copy(ciphertexts,shuffledCiphertext)
	}
	fmt.Printf("Each of the %v players performed the shuffle successfully \n", len(players))
	
	// Decryption
	outer:
	for idx := range players{
		decryptedMsgNew := players[idx].Decrypt(pubParams, ciphertexts[idx], players)
		for card := range OrgCards{
			if OrgCards[card].Cmp(decryptedMsgNew) == 0 {
				fmt.Printf("Player %v decrypted card %v to obtain the value: %v \n", players[idx].Id , idx, card)
				continue outer
			}	
		}
	}
	// Reset stdout to console
    os.Stdout = os.NewFile(uintptr(syscall.Stdout), "/dev/stdout")
}

