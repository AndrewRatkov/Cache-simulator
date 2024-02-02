#include <iostream>
#include <stdio.h>
#include <vector>
#include <cassert>
#include <unordered_map>

#define M 64
#define N 60
#define K 32

int8_t a[M][K];
int16_t b[K][N];
int32_t c[M][N];


const int MEM_SIZE = 1 << 19;
const int CACHE_LINE_COUNT = 64;
const int CACHE_LINE_SIZE = 32;
const int CACHE_SIZE = CACHE_LINE_COUNT * CACHE_LINE_SIZE;
const int ADDR_LEN = 19; // log(MEM_SIZE)
const int CACHE_OFFSET_LEN = 5; // log(CACHE_LINE_SIZE)
const int CACHE_TAG_LEN = 10;
const int CACHE_IDX_LEN = ADDR_LEN - CACHE_TAG_LEN - CACHE_OFFSET_LEN; // 4
const int CACHE_WAY = 4; // CACHE_LINE_COUNT >> CACHE_IDX_LEN
const int CACHE_SETS_COUNT = 16; // (1 << CACHE_IDX_LEN)

// all these 6 coonstants are useless
const int ADDR1_BUS_LEN = ADDR_LEN;
const int ADDR2_BUS_LEN = 14;
const int DATA1_BUS_LEN = 16;
const int DATA2_BUS_LEN = 16;
const int CTR1_BUS_LEN = 3;
const int CTR2_BUS_LEN = 2;

// constants
const int TIME_DELETE_UNSAVED = 101; // sending cache line from cache to MEM and saving it in MEM
const int TIME_READ_WHEN_FOUND = 6; // reading cacheline when it is in cache
const int TIME_READ_WHEN_NOT_FOUND = 121; // reading cacheline when it is not in cache:
const int TIME_WRITE_WHEN_FOUND = 6; // writing to a cacheline when it is in cache
const int TIME_WRITE_WHEN_NOT_FOUND = 121; // writing to a cacheline when it is not in cache


// for debug
int LRU_TIMES_READ_FOUND = 0; // hits while reading
int LRU_TIMES_READ_NOT_FOUND = 0; // misses while reading
int LRU_TIMES_WRITE_FOUND = 0; // hits while founding
int LRU_TIMES_WRITE_NOT_FOUND = 0; // misses while founding
int LRU_TIMES_DELETE_AND_SAVE_TO_MEM = 0; // savings from cache to MEM

int BIT_PLRU_TIMES_READ_FOUND = 0; // hits while reaading
int BIT_PLRU_TIMES_READ_NOT_FOUND = 0; // misses while reading
int BIT_PLRU_TIMES_WRITE_FOUND = 0; // hits while founding
int BIT_PLRU_TIMES_WRITE_NOT_FOUND = 0; // misses while founding
int BIT_PLRU_TIMES_DELETE_AND_SAVE_TO_MEM = 0; // savings from cache to MEM

int add_assign=0; // number of +=
int assign=0; // number of =
int mul=0; //  number of *
int inc=0; // number of ++
int compares=0; // number of GOTO commands in fors 

unsigned lce(unsigned A, unsigned C, unsigned MOD, unsigned seed) {
 return (A * seed + C) % MOD;
}

enum struct Policy{
    LRU = 0,
    bit_pLRU = 1
};

enum struct COMMAND1{
    READ8=0, // read 8 bytes
    READ16=1, // read 16 bytes
    READ32=2, // read 32 bytes
    WRITE8=3, // write 8 bytes
    WRITE16=4, // write 16 bytes
    WRITE32=5, // write 32 bytes
//    RESPONSE=6
};

int TIME_FOR_DATA(COMMAND1 cmd) {
    if (cmd == COMMAND1::READ8 || cmd == COMMAND1::READ16 || cmd == COMMAND1::WRITE8 || cmd == COMMAND1::WRITE16) {
        return 1;
    }
    return 2;
}

struct Address {
    int value;

    int offset() const { // last CACHE_OFFSET_LEN bits 
        return value & ((1 << CACHE_OFFSET_LEN) - 1);
    }

    int idx() const { // middle CACHE_IDX_LEN bits
        return (value >> CACHE_OFFSET_LEN) & ((1 << CACHE_IDX_LEN) - 1);
    }

    int tag() const { // first CACHE_TAG_LEN bits
        return value >> (CACHE_OFFSET_LEN + CACHE_IDX_LEN);
    }
};

struct CacheLine {
    int tag;
    bool valid;
    bool dirty;
    char f;

    int tacts_to_remove_from_stack() {
        return ((valid && dirty) ? TIME_DELETE_UNSAVED : 0);
    }

    void print() {
        printf("tag: ");
        for (int i = CACHE_TAG_LEN - 1; i >= 0; i--) printf("%d", (tag & (1 << i) ? 1 : 0));
        printf("\t valid: ");
        if (valid) printf("true\t");
        else printf("false\t");
        printf("dirty: ");
        if (dirty) printf("true \t");
        else printf("false\t");
        printf("flag: %d\n", f);
    }
};

struct info_op{
    bool HITS;
    int TACTS;

    void print() {
        printf("HITS: %d\t TACTS: %d\n", HITS, TACTS);
    }
};

struct CacheSet {
    std::vector<CacheLine> SET;

    void init() {
        SET.assign(CACHE_WAY, {0, false, false, 0});
    }

    bool is_not_filled() {
        for (int i = 0; i < CACHE_WAY; i++) {
            if (!SET[i].valid) return true;
        }
        return false;
    }
    
    int first_not_filled() {
        for (int i = 0; i < CACHE_WAY; i++) {
            if (!SET[i].valid) return i;
        }
        return CACHE_WAY;
    }

    void renumerate(int i, Policy pol) { // renumeration of cacheset if i-th cacheline is changed
        assert(0 <= i && i < CACHE_WAY);
        
        if (pol == Policy::LRU) {
            for (int j = 0; j < CACHE_WAY; j++) {
                if (j != i && SET[j].valid && (SET[j].f < SET[i].f || !SET[i].valid)) {
                    SET[j].f++;
                }
            }
            SET[i].f = 0;
        } else {
            int count_valid_1 = 0;
            for (int j = 0; j < CACHE_WAY; j++) {
                count_valid_1 += ((i != j) && SET[j].valid && (SET[j].f == 1));
            }
            if (count_valid_1 == CACHE_WAY - 1) {
                for (int j = 0; j < CACHE_WAY; j++) {
                    SET[j].f = (i == j);
                }
            } else {
                SET[i].f = 1;
            }
        }

    }

    info_op compute(Address addr, COMMAND1 cmd, Policy pol) {
        int tag = addr.tag();

        // if reading
        if (cmd == COMMAND1::READ8 || cmd == COMMAND1::READ16 || cmd == COMMAND1::READ32) {
            for (int i = 0; i < CACHE_WAY; i++) {
                if (SET[i].valid && SET[i].tag == tag) { // found address
                    renumerate(i, pol);

                    (pol == Policy::LRU) ? LRU_TIMES_READ_FOUND++ : BIT_PLRU_TIMES_READ_FOUND++; // for debug
                    
                    return {true, TIME_READ_WHEN_FOUND};
                }
            }
            // address not found
            int i;
            if (is_not_filled()) {
                i = first_not_filled();
            } else {
                i = 0;
                if (pol == Policy::LRU) {
                    while (SET[i].f != 3) i++;
                } else {
                    while (SET[i].f != 0) i++;
                }
            }
            assert(i < CACHE_WAY);
            int ADD = SET[i].tacts_to_remove_from_stack();
            SET[i].dirty = false;
            SET[i].tag = tag;
            renumerate(i, pol);
            SET[i].valid = true;

            if (pol == Policy::LRU) { // for debug
                LRU_TIMES_READ_NOT_FOUND++;
                if (ADD) LRU_TIMES_DELETE_AND_SAVE_TO_MEM++;
            } else {
                BIT_PLRU_TIMES_READ_NOT_FOUND++;
                if (ADD) BIT_PLRU_TIMES_DELETE_AND_SAVE_TO_MEM++;
            }

            return {false, TIME_READ_WHEN_NOT_FOUND + ADD};
        } else { // if writing
            
            for (int i = 0; i < CACHE_WAY; i++) {
                if (SET[i].valid && SET[i].tag == tag) { // found address
                    SET[i].dirty = true;
                    renumerate(i, pol);

                    (pol == Policy::LRU) ? LRU_TIMES_WRITE_FOUND++ : BIT_PLRU_TIMES_WRITE_FOUND++;  // for debug
                    
                    return {true, TIME_WRITE_WHEN_FOUND};
                }
            }
            // address not found
            int i;
            if (is_not_filled()) {
                i = first_not_filled();
            } else {
                i = 0;
                if (pol == Policy::LRU) {
                    while (SET[i].f != 3) i++;
                } else {
                    while (SET[i].f != 0) i++;
                }
            }
            assert(i < CACHE_WAY);
            int ADD = SET[i].tacts_to_remove_from_stack();
            SET[i].dirty = true;
            SET[i].tag = tag;
            renumerate(i, pol);
            SET[i].valid = true;

            (pol == Policy::LRU) ? LRU_TIMES_WRITE_NOT_FOUND++ : BIT_PLRU_TIMES_WRITE_NOT_FOUND++; // for debug
            if (ADD) {
                (pol == Policy::LRU) ? LRU_TIMES_DELETE_AND_SAVE_TO_MEM++ : BIT_PLRU_TIMES_DELETE_AND_SAVE_TO_MEM++;
            }

            return {false, TIME_WRITE_WHEN_NOT_FOUND + ADD};
        }

    }

    void print() {
        printf("\n");
        for (int i = 0; i < CACHE_WAY; i++) {
            SET[i].print();
        }
        printf("\n");
    }

};

struct Cache {
    CacheSet sets[CACHE_SETS_COUNT];

    void init() {
        for (int i = 0; i < CACHE_SETS_COUNT; i++) {
            sets[i].init();
        }
    }

    void print() {
        for (int i = 0; i < CACHE_SETS_COUNT; i++) {
            printf("set #%d\n", i);
            sets[i].print();
        }
    }

    info_op compute(Address addr, COMMAND1 cmd, Policy pol) {
        return sets[addr.idx()].compute(addr, cmd, pol);
    }
};

int main() {
    int pointer = (1 << 18);
    // сопоставим каждому элементу каждой матрицы указатель на его начало в MEMe

    std::unordered_map<int, int> a_i_j_to_pointer;
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < K; j++) {
            a_i_j_to_pointer[i * K + j] = pointer;
            pointer += 1;
        }
    }

    std::unordered_map<int, int> b_i_j_to_pointer;
    for (int i = 0; i < K; i++) {
        for (int j = 0; j < N; j++) {
            b_i_j_to_pointer[i * N + j] = pointer;
            pointer += 2;
        }
    }

    std::unordered_map<int, int> c_i_j_to_pointer;
    for (int i = 0; i < M; i++) {
        for (int j = 0; j < N; j++) {
            c_i_j_to_pointer[i * N + j] = pointer;
            pointer += 4;
        }
    }

    Cache lru_cache;
    lru_cache.init();
    Cache bit_plru_cache;
    bit_plru_cache.init();

    int lru_tacts = 0;
    int bit_plru_tacts = 0;

    int lru_hits = 0;
    int bit_plru_hits = 0;

    int lru_misses = 0;
    int bit_plru_misses = 0;


    int PA = 0, PC = 0;
    assign += 2; // init PA, PC
    assign++; // init y
    for (int y = 0; y < M; y++) {
        compares++; // y < M at the beginning of the loop
        inc++; // y++ at the end of the loop
        assign++; // init x
        for (int x = 0; x < N; x++) {
            compares++; // x < N at the beginning of the loop
            inc++; // x++ at the end of the loop
            int PB = 0; // int s = 0;
            assign += 2; // init PB, S
            assign++; // init k
            for (int k = 0; k < K; k++) {
                compares++; // k < K at the beginning of the loop
                inc++; // k++ at the end of the loop
                auto lru1 = lru_cache.compute({a_i_j_to_pointer[PA + k]}, COMMAND1::READ8, Policy::LRU); // get pa[k] fromm lru cache
                auto lru2 = lru_cache.compute({b_i_j_to_pointer[PB + x]}, COMMAND1::READ16, Policy::LRU); // get pb[x] from lru cache
                lru_tacts += lru1.TACTS + lru2.TACTS;
                lru_hits += (int)lru1.HITS + (int)lru2.HITS;
                lru_misses += (int)(!lru1.HITS) + (int)(!lru2.HITS);

                auto bit_plru1 = bit_plru_cache.compute({a_i_j_to_pointer[PA + k]}, COMMAND1::READ8, Policy::bit_pLRU); // get pa[k] fromm bit_lru cache
                auto bit_plru2 = bit_plru_cache.compute({b_i_j_to_pointer[PB + x]}, COMMAND1::READ16, Policy::bit_pLRU); // get pb[x] fromm bit_plru cache
                bit_plru_tacts += bit_plru1.TACTS + bit_plru2.TACTS;
                bit_plru_hits += (int)bit_plru1.HITS + (int)bit_plru2.HITS;
                bit_plru_misses += (int)(!bit_plru1.HITS) + (int)(!bit_plru2.HITS);

                PB += N;
                mul++; // multiplication
                add_assign += 2; // changed PC, s
            }
            auto lru3 = lru_cache.compute({c_i_j_to_pointer[PC + x]}, COMMAND1::WRITE32, Policy::LRU);
            lru_tacts += lru3.TACTS;
            if (lru3.HITS) lru_hits++;
            else lru_misses++;

            auto bit_plru3 = bit_plru_cache.compute({c_i_j_to_pointer[PC + x]}, COMMAND1::WRITE32, Policy::bit_pLRU);
            bit_plru_tacts += bit_plru3.TACTS;
            if (bit_plru3.HITS) bit_plru_hits++;
            else bit_plru_misses++;

        }
        PA += K; PC += N;
        add_assign += 2; // changed PA, PC
    }


    // printf("LRU: tacts: %d\t hits:%d\t misses:%d\n", tacts + lru_tacts, lru_hits, lru_misses);
    // printf("bit-pLRU: tacts: %d\t hits:%d\t misses:%d\n", tacts + bit_plru_tacts, bit_plru_hits, bit_plru_misses);


    // debug things
    // printf(" +++LRU info (without deleting at the end):+++\n LRU_TIMES_READ_FOUND: %d\n LRU_TIMES_READ_NOT_FOUND: %d\n LRU_TIMES_WRITE_FOUND: %d\n LRU_TIMES_WRITE_NOT_FOUND: %d\n LRU_TIMES_DELETE_AND_SAVE_TO_MEM: %d\n", LRU_TIMES_READ_FOUND, LRU_TIMES_READ_NOT_FOUND, LRU_TIMES_WRITE_FOUND, LRU_TIMES_WRITE_NOT_FOUND, LRU_TIMES_DELETE_AND_SAVE_TO_MEM);
    // printf(" +++BIT_PLRU info (without deleting at the end):+++\n BIT_PLRU_TIMES_READ_FOUND: %d\n BIT_PLRU_TIMES_READ_NOT_FOUND: %d\n BIT_PLRU_TIMES_WRITE_FOUND: %d\n BIT_PLRU_TIMES_WRITE_NOT_FOUND: %d\n BIT_PLRU_TIMES_DELETE_AND_SAVE_TO_MEM: %d\n", BIT_PLRU_TIMES_READ_FOUND, BIT_PLRU_TIMES_READ_NOT_FOUND, BIT_PLRU_TIMES_WRITE_FOUND, BIT_PLRU_TIMES_WRITE_NOT_FOUND, BIT_PLRU_TIMES_DELETE_AND_SAVE_TO_MEM);
    // printf("add_assign %d\n", add_assign);
    // printf("assign %d\n", assign);
    // printf("inc %d\n", inc);
    // printf("mul %d\n", mul);
 
    int tacts = add_assign + assign + mul * 7 + inc + compares + 1; 
    // printf("tacts: %d\n", tacts); // tacts in main
    
    printf("LRU:\thit perc. %3.4f%%\ttime: %u\npLRU:\thit perc. %3.4f%%\ttime: %u\n", 100 * (double)(lru_hits) / (lru_hits + lru_misses), tacts + lru_tacts, 100 * (double)(bit_plru_hits) / (bit_plru_hits + bit_plru_misses), tacts + bit_plru_tacts);


    return 0;
}
