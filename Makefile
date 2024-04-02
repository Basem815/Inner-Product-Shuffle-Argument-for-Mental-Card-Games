build:
	go build -o ./bin/block-chain
run: build
	./bin/block-chain
test:
	go test ./...
	