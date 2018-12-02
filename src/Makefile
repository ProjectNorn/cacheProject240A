CXX=g++
OPTS=-g -Werror -std=c++11

all: main.o cache.o
	$(CXX) $(OPTS) -lm -o cache main.o cache.o

main.o: main.cpp cache.h
	$(CXX) $(OPTS) -c main.cpp

cache.o: cache.h cache.cpp
	$(CXX) $(OPTS) -c cache.cpp

clean:
	rm -f *.o cache;
