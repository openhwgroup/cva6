CC = g++
TARGETS = Decapsuler
CFLAGS = -Wall -Wextra -g

all: $(TARGETS)

Decapsuler: Decapsuler.cpp
	$(CC) -o Decapsuler Decapsuler.cpp $(CFLAGS)

.PHONY: clean

clean:
	rm -f $(TARGETS)

clean_all:
	rm -f $(TARGETS)
	rm -rf receiver_data
