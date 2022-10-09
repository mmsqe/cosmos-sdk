package secp256k1

import (
	"fmt"
)

func main() {
	b := []byte(`hello world`)
	pubkey, _ := RecoverPubkey(b, b)
	fmt.Printf("%x\n", pubkey)
}
