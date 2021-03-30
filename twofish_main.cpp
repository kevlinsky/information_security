#include <cstring>
#include <cassert>
#include <iostream>

typedef unsigned char Twofish_Byte;
typedef unsigned int Twofish_UInt32;

typedef Twofish_Byte Qtype;

#define q0  q_table[0]

#define q1  q_table[1]

#define H02(y, L)  MDS_table[0][q0[q0[y]^L[ 8]]^L[0]]
#define H12(y, L)  MDS_table[1][q0[q1[y]^L[ 9]]^L[1]]
#define H22(y, L)  MDS_table[2][q1[q0[y]^L[10]]^L[2]]
#define H32(y, L)  MDS_table[3][q1[q1[y]^L[11]]^L[3]]


class TwofishKey {
public:
    TwofishKey() {
        Clear();
    }

    void Clear() {
        memset(this, 0, sizeof(*this));
    }

    Twofish_UInt32 s[4][256];
    Twofish_UInt32 K[40];
};

class Twofish {
    unsigned int rs_poly_const[2] = {0, 0x14d};
    unsigned int rs_poly_div_const[2] = {0, 0xa6};
    Twofish_Byte t_table[2][4][16] = {{{0x8, 0x1, 0x7, 0xD, 0x6, 0xF, 0x3, 0x2, 0x0, 0xB, 0x5, 0x9, 0xE, 0xC, 0xA, 0x4},
                                                              {0xE, 0xC, 0xB, 0x8, 0x1, 0x2, 0x3, 0x5, 0xF, 0x4, 0xA, 0x6, 0x7, 0x0, 0x9, 0xD},
                                                              {0xB, 0xA, 0x5, 0xE, 0x6, 0xD, 0x9, 0x0, 0xC, 0x8, 0xF, 0x3, 0x2, 0x4, 0x7, 0x1},
                                                              {0xD, 0x7, 0xF, 0x4, 0x1, 0x2, 0x6, 0xE, 0x9, 0xB, 0x3, 0x0, 0x8, 0x5, 0xC, 0xA}},
                                                             {{0x2, 0x8, 0xB, 0xD, 0xF, 0x7, 0x6, 0xE, 0x3, 0x1, 0x9, 0x4, 0x0, 0xA, 0xC, 0x5},
                                                              {0x1, 0xE, 0x2, 0xB, 0x4, 0xC, 0x3, 0x7, 0x6, 0xD, 0xA, 0x5, 0xF, 0x9, 0x0, 0x8},
                                                              {0x4, 0xC, 0x7, 0x5, 0x1, 0x6, 0x9, 0xA, 0x0, 0xE, 0xD, 0x8, 0x2, 0xB, 0x3, 0xF},
                                                              {0xB, 0x9, 0x5, 0x1, 0xC, 0x3, 0xD, 0xE, 0x6, 0x4, 0x7, 0xF, 0x2, 0x0, 0x8, 0xA}}};
    Twofish_UInt32 mds_poly_divx_const[2] = {0, 0xb4};

public:

    Twofish() {
        initialise_q_boxes();
        initialise_mds_tables();
    }

    void PrepareKey(const Twofish_Byte key[], int key_len, TwofishKey *xkey) {
        Twofish_Byte K[32 + 32 + 4];

        int kCycles;

        int i;
        Twofish_UInt32 A, B;

        Twofish_Byte *kptr;
        Twofish_Byte *sptr;
        Twofish_Byte *t;

        Twofish_Byte b, bx, bxx;


        memcpy(K, key, key_len);
        memset(K + key_len, 0, sizeof(K) - key_len);

        kCycles = 2;

        for (i = 0; i < 40; i += 2) {

            A = h(i, K, kCycles);
            B = h(i + 1, K + 4, kCycles);
            B = ((B) << (8) | ((B) & ((((Twofish_UInt32) 2) << 31) - 1)) >> (32 - (8)));

            A += B;
            B += A;
            xkey->K[i] = A;
            xkey->K[i + 1] = ((B) << (9) | ((B) & ((((Twofish_UInt32) 2) << 31) - 1)) >> (32 - (9)));
        }

        A = B = 0;

        kptr = K + 8 * kCycles;
        sptr = K + 32;

        while (kptr > K) {
            kptr -= 8;

            memset(sptr, 0, 4);
            memcpy(sptr + 4, kptr, 8);

            t = sptr + 11;
            while (t > sptr + 3) {
                b = *t;
                bx = (Twofish_Byte) ((b << 1) ^ rs_poly_const[b >> 7]);
                bxx = (Twofish_Byte) ((b >> 1) ^ rs_poly_div_const[b & 1] ^ bx);

                t[-1] ^= bxx;
                t[-2] ^= bx;
                t[-3] ^= bxx;
                t[-4] ^= b;

                t--;
            }

            sptr += 8;
        }

        b = bx = bxx = 0;

        fill_keyed_sboxes(&K[32], kCycles, xkey);
        memset(K, 0, sizeof(K));
    }

    void Encrypt(const TwofishKey *xkey, const Twofish_Byte p[16], Twofish_Byte c[16]) {
        Twofish_UInt32 A, B, C, D, T0, T1;

        get_input(p, A, B, C, D, xkey, 0);

        encrypt(A, B, C, D, T0, T1, xkey);

        put_output(C, D, A, B, c, xkey, 4);
    }

    void Decrypt(const TwofishKey *xkey, const Twofish_Byte c[16], Twofish_Byte p[16]) {
        Twofish_UInt32 A, B, C, D, T0, T1;

        get_input(c, A, B, C, D, xkey, 4);

        decrypt(A, B, C, D, T0, T1, xkey);

        put_output(C, D, A, B, p, xkey, 0);
    }


private:

    static Twofish_UInt32 rol_32(Twofish_UInt32 x, int n) {
        return x << n | (x & ((((Twofish_UInt32) 2) << 31) - 1)) >> (32 - n);
    }

    static Twofish_UInt32 ror_32(Twofish_UInt32 x, int n) {
        return x >> n | (x & ((((Twofish_UInt32) 2) << 31) - 1)) << (32 - n);
    }

    static Twofish_UInt32 bswap(Twofish_UInt32 x) {
        return rol_32(x, 8) & 0x00ff00ff | ror_32(x, 8) & 0xff00ff00;
    }

    static Twofish_UInt32 select_byte(Twofish_UInt32 x, int b) {
        return (x >> (8 * b)) & 0xff;
    }

    static Twofish_UInt32 b0(Twofish_UInt32 x) {
        return select_byte(x, 0);
    }

    static Twofish_UInt32 b1(Twofish_UInt32 x) {
        return select_byte(x, 1);
    }

    static Twofish_UInt32 b2(Twofish_UInt32 x) {
        return select_byte(x, 2);
    }

    static Twofish_UInt32 b3(Twofish_UInt32 x) {
        return select_byte(x, 3);
    }

    static Twofish_UInt32 get_32(const Twofish_Byte *p) {
        return (Twofish_UInt32) (p[0]) | (Twofish_UInt32) (p[1]) << 8 | (Twofish_UInt32) (p[2]) << 16 |
               (Twofish_UInt32) (p[3]) << 24;
    }

    static void put_32(Twofish_UInt32 v, Twofish_Byte *p) {
        p[0] = (Twofish_Byte) (v & 0xff);
        p[1] = (Twofish_Byte) ((v >> 8) & 0xff);
        p[2] = (Twofish_Byte) ((v >> 16) & 0xff);
        p[3] = (Twofish_Byte) ((v >> 24) & 0xff);
    }

    static int ror_4_by_1(int x){
        return (x >> 1) | ((x << 3) & 0x8);
    }

    static Twofish_UInt32 g0(Twofish_UInt32 x, const TwofishKey *xkey){
        return xkey->s[0][b0(x)] ^ xkey->s[1][b1(x)] ^ xkey->s[2][b2(x)] ^ xkey->s[3][b3(x)];
    }
    static Twofish_UInt32 g1(Twofish_UInt32 x, const TwofishKey *xkey){
        return xkey->s[0][b3(x)] ^ xkey->s[1][b0(x)] ^ xkey->s[2][b1(x)] ^ xkey->s[3][b2(x)];
    }

    static void encrypt_rnd(Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, Twofish_UInt32 t0, Twofish_UInt32 t1, const TwofishKey *xkey, int r){
        t0 = g0(a, xkey);
        t1 = g1(b, xkey);
        c ^= t0 + t1 + xkey->K[8+2*(r)];
        c = ror_32(c,1);
        d = rol_32(d,1);
        d ^= t0 + 2 * t1 + xkey->K[8 + 2 * r+1];
    }

    static void encrypt_cycle(Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, Twofish_UInt32 t0, Twofish_UInt32 t1, const TwofishKey *xkey, int r){
        encrypt_rnd(a, b, c, d, t0, t1, xkey, 2 * r);
        encrypt_rnd(c, d, a, b, t0, t1, xkey, 2 * r + 1);
    }

    static void encrypt(Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, Twofish_UInt32 t0, Twofish_UInt32 t1, const TwofishKey *xkey){
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 0);
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 1);
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 2);
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 3);
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 4);
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 5);
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 6);
        encrypt_cycle(a, b, c, d, t0, t1, xkey, 7);
    }

    static void decrypt_rnd(Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, Twofish_UInt32 t0, Twofish_UInt32 t1, const TwofishKey *xkey, int r){
        t0 = g0(a, xkey);
        t1 = g1(b, xkey);
        c = rol_32(c, 1);
        c ^= t0 + t1 + xkey->K[8 + 2 * r];
        d ^= t0 + 2 * t1 + xkey->K[8 + 2 * r + 1];
        d = ror_32(d, 1);
    }

    static void decrypt_cycle(Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, Twofish_UInt32 t0, Twofish_UInt32 t1, const TwofishKey *xkey, int r){
        decrypt_rnd(a, b, c, d, t0, t1, xkey, 2 * r + 1);
        decrypt_rnd(a, b, c, d, t0, t1, xkey, 2 * r);
    }

    static void decrypt(Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, Twofish_UInt32 t0, Twofish_UInt32 t1, const TwofishKey *xkey){
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 7);
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 6);
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 5);
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 4);
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 3);
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 2);
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 1);
        decrypt_cycle(a, b, c, d, t0, t1, xkey, 0);
    }

    static void get_input(const Twofish_Byte *src, Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, const TwofishKey *xkey, int koff){
        a = get_32(src) ^ xkey->K[ koff];
        b = get_32(src+ 4) ^ xkey->K[1 + koff];
        c = get_32(src+ 8) ^ xkey->K[2 + koff];
        d = get_32(src+12) ^ xkey->K[3 + koff];
    }

    static void put_output(Twofish_UInt32 a, Twofish_UInt32 b, Twofish_UInt32 c, Twofish_UInt32 d, Twofish_Byte* dst, const TwofishKey *xkey, int koff){
        a ^= xkey->K[koff];
        b ^= xkey->K[1+koff];
        c ^= xkey->K[2+koff];
        d ^= xkey->K[3+koff];
        put_32(a, dst);
        put_32(b, dst + 4);
        put_32(c, dst + 8 );
        put_32(d, dst + 12 );
    }

    static void make_q_table(const Twofish_Byte t[4][16], Qtype q[256]) {
        int a, b, c, d;
        int i;

        for (i = 0; i < 256; i++) {
            a = i >> 4;
            b = i & 0xf;
            c = a ^ b;
            d = a ^ ror_4_by_1(b) ^ ((a << 3) & 8);
            a = t[0][c];
            b = t[1][d];
            c = a ^ b;
            d = a ^ ror_4_by_1(b) ^ ((a << 3) & 8);
            a = t[2][c];
            b = t[3][d];

            q[i] = (Qtype) ((b << 4) | a);
        }
    }

    void initialise_q_boxes() {
        make_q_table(t_table[0], q_table[0]);
        make_q_table(t_table[1], q_table[1]);
    }

    void initialise_mds_tables() {
        int i;
        Twofish_UInt32 q, qef, q5b;

        for (i = 0; i < 256; i++) {
            q = q_table[0][i];

            qef = (q >> 1) ^ mds_poly_divx_const[q & 1];

            q5b = (qef >> 1) ^ mds_poly_divx_const[qef & 1] ^ q;

            qef ^= q5b;

            MDS_table[1][i] = (q << 24) | (q5b << 16) | (qef << 8) | qef;
            MDS_table[3][i] = (q5b << 24) | (qef << 16) | (q << 8) | q5b;

            q = q_table[1][i];
            qef = (q >> 1) ^ mds_poly_divx_const[q & 1];
            q5b = (qef >> 1) ^ mds_poly_divx_const[qef & 1] ^ q;
            qef ^= q5b;

            MDS_table[0][i] = (qef << 24) | (qef << 16) | (q5b << 8) | q;
            MDS_table[2][i] = (qef << 24) | (q << 16) | (qef << 8) | q5b;
        }
    }

    Twofish_UInt32 h(int k, Twofish_Byte L[], int kCycles) {
        return H02(k, L) ^ H12(k, L) ^ H22(k, L) ^ H32(k, L);
    }

    void fill_keyed_sboxes(Twofish_Byte S[], int kCycles, TwofishKey *xkey) {
        for (int i = 0; i < 256; i++) {
            xkey->s[0][i] = H02(i, S);
            xkey->s[1][i] = H12(i, S);
            xkey->s[2][i] = H22(i, S);
            xkey->s[3][i] = H32(i, S);
        }
    }

    Qtype q_table[2][256];
    Twofish_UInt32 MDS_table[4][256];
};

int main(){
    int n;

    std::cout << "Type in the length of the key:" << std::endl;
    std::cin >> n;

    Twofish twofish;

    TwofishKey xkey;
    Twofish_Byte key[n];
    std::cout << "Type in the key:" << std::endl;
    std::cin >> key;
    twofish.PrepareKey(key, n, &xkey);

    Twofish_Byte in[n];
    std::cout << "Type in the str:" << std::endl;
    std::cin >> in;

    Twofish_Byte tmp[n];
    twofish.Encrypt(&xkey, in, tmp);

    std::cout << "Encrypted data:" << std::endl;
    for (unsigned char i : tmp){
        std::cout << (int)i << " ";
    }
    std::cout << std::endl;

    Twofish_Byte out[n];
    twofish.Decrypt(&xkey, out, tmp);

    std::cout << "Decrypted data:" << std::endl;
    for (unsigned char i : tmp){
        std::cout << (int)i << " ";
    }
    std::cout << std::endl;

    return 0;
}