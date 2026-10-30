CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -Werror -pedantic -O2
CPPFLAGS += -Iinclude

SRCS := $(wildcard src/*.c)
OBJS := $(patsubst src/%.c,build/%.o,$(SRCS))
TESTS := $(patsubst tests/%.c,build/%,$(wildcard tests/test_*.c))

.PHONY: all test clean

all: build/libct.a

build:
	mkdir -p build

build/%.o: src/%.c | build
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

build/libct.a: $(OBJS)
	ar rcs $@ $^

build/test_%: tests/test_%.c build/libct.a
	$(CC) $(CPPFLAGS) $(CFLAGS) $< build/libct.a -o $@

test: $(TESTS)
	@set -e; for t in $(TESTS); do echo "== $$t"; ./$$t; done

clean:
	rm -rf build
