CC = g++
CFLAGS = -std=c++17 -O2 -Wall -Wextra -Werror -pedantic -Wno-unused-result -Wconversion -Wvla

TARGET = main

all: clean $(TARGET)

$(TARGET): main.cpp
	$(CC) $(CFLAGS) main.cpp -o $(TARGET)

clean:
	rm -f $(OBJ) $(TARGET)
