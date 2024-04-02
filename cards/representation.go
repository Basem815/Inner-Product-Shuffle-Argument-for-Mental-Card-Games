package cards

import (
	"main/preprocessing"
	"math/big"
	"strconv"
)


type Card struct {
	value, suit string
}  

type Suit int


const (
	Spades Suit = iota
	Hearts
	Diamonds
	Clubs
)

func CreateDeck(numSuits, numCards int) []Card{
	if numSuits > 4 {
		panic("Cannot have more than 4 suits")
	}
	deck := []Card{}
	for i:= 0; i < numSuits; i++ {
		for j:= 0; j < numCards; j++ {
			val := strconv.Itoa(j+1)
			if val == "1" {
				val = "A"
			}else if val == "11"{
				val = "J"
			}else if val == "12"{
				val = "Q"
			}else if val == "13"{
				val = "K"
			}
			deck = append(deck, newCard(val, suitToUnicode(Suit(i))))
		}
	}
	return deck
}

func newCard(v, s string ) Card {
	return Card{
		value: v,
		suit: s,
	}
}


/* cardVal is a pointer so cannot simply check if it exists inside a set*/
func GroupEltToCard(pp preprocessing.PublicParameters, orgDeck []Card, cardVal *big.Int) Card{

	reversedMap := ReverseMap(CardsToGroupElts(pp, orgDeck))
	for key := range reversedMap{
		if key.Cmp(cardVal) == 0 {
			return reversedMap[key]
		}
	}
	return reversedMap[cardVal]
}

func ReverseMap(m map[Card]*big.Int) map[*big.Int]Card {
    n := make(map[*big.Int]Card, len(m))
    for k, v := range m {
        n[v] = k
    }
    return n
}

// Represent them as members of the group G
func CardsToGroupElts(pp preprocessing.PublicParameters, deck []Card) map[Card]*big.Int {

	cards_conv:= map[Card]*big.Int{}
	x := 2
	for _, card_val := range deck{
		cards_conv[card_val] =  new(big.Int).Exp(pp.GetGeneratorG(), big.NewInt(int64(x)),pp.GetPrimeP() )
		x ++ 
	}
	return cards_conv

}

func suitToUnicode(s Suit) string {
	switch s {
	case Spades:
		return "♠"
	case Hearts:
		return "♥"
	case Diamonds:
		return "♦"
	case Clubs:
		return "♣"
	default:
		panic("Invalid card suit")
	}
}