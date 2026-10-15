CXX ?= g++
CXXFLAGS ?= -O3 -march=native -std=c++17 -Wall -Wextra -Wno-sign-compare -pthread
VERIFIER = PYTHONPATH=external/Andrews-Curtis/competition/tools

.PHONY: all clean test endgame

all: bin/acengine

bin/acengine: engine/*.cpp engine/*.hpp
	@mkdir -p bin
	$(CXX) $(CXXFLAGS) engine/main.cpp -o $@

# Shared endgame table (backward BFS from the target).  Radius 6 is fast
# to build; 7 is larger but a bigger target for every search.
endgame: bin/acengine
	@mkdir -p data
	./bin/acengine build-endgame --radius $${R:-7} --out data/endgame_r$${R:-7}.bin

test: bin/acengine
	python3 -m pytest -q tests

clean:
	rm -rf bin
