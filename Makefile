all: main.cpp
	g++ -o sample main.cpp /opt/homebrew/Cellar/stp/2.3.3_4/lib/libstp.dylib -I /opt/homebrew/Cellar/stp/2.3.3_4/include
	./out