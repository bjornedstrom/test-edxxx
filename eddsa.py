# -*- coding: utf-8 -*-
# Draft1. Björn Edström <be@bjrn.se> based on Ed25519 code and EdDSA spec.

# https://github.com/gvanas/KeccakCodePackage
import CompactFIPS202
import hashlib


def le2int(buf):
    """little endian buffer to integer."""
    integer = 0
    shift = 0
    for byte in buf:
        integer |= byte << shift
        shift += 8
    return integer


def int2le(integer, pad):
    """integer to little endian buffer."""
    buf = []
    while integer:
        buf.append(integer & 0xff)
        integer >>= 8
        pad -= 1
    if pad < 0:
        raise ValueError('data too long to pad further')
    while pad > 0:
        buf.append(0)
        pad -= 1
    return bytearray(buf)


class EdDSA(object):
    b = None # bits
    q = None # prime
    l = None # order
    B = None # base point (x, y)
    d = None # edwards equation
    a = None # edwards equation
    c = None # cofactor

    def Hint(self, m):
        return le2int(self.H(m))

    def inv(self, x):
        p = pow(x, self.q-2, self.q)
        return p

    def edwards(self, P, Q):
        x1 = P[0]
        y1 = P[1]
        x2 = Q[0]
        y2 = Q[1]
        x3 = (x1*y2+x2*y1) * self.inv(1+self.d*x1*x2*y1*y2)
        y3 = (y1*y2-self.a*x1*x2) * self.inv(1-self.d*x1*x2*y1*y2)
        return [x3 % self.q,y3 % self.q]

    def scalarmult(self, P, e):
        if e == 0:
            return [0,1]
        Q = self.scalarmult(P,e//2)
        Q = self.edwards(Q,Q)
        if e & 1:
            Q = self.edwards(Q,P)
        return Q

    def encodeint(self, y):
        return int2le(y, self.b//8)

    def encodepoint(self, P):
        x = P[0]
        y = P[1]
        return self.encodeint(((x & 1) << (self.b - 1)) + y)

    def bit(self,h,i):
        return (h[i//8] >> (i%8)) & 1

    def isoncurve(self, P):
        x = P[0]
        y = P[1]
        return (-x*x + y*y - 1 - self.d*x*x*y*y) % self.q == 0

    def decodeint(self, s):
        return le2int(s)

    def decodepoint(self,s):
        tmp_int = le2int(s)
        highest_bit = 0
        if tmp_int & (1 << (self.b - 1)):
            tmp_int -= (1 << (self.b - 1))
            highest_bit = 1
        y = tmp_int

        x = self.xrecover(y)
        if x & 1 != highest_bit:
            x = self.q-x
        P = [x,y]
        if not self.isoncurve(P):
            raise Exception("decoding point that is not on curve")
        return P

    def publickey(self, sk):
        h = self.H(sk)
        # XXX: Setting high bit (constant time montgomery ladder)
        # XXX: Clearing the lowest c bits.
        a = 2**(self.n) + sum(2**i * self.bit(h,i) for i in range(self.c,self.n))
        A = self.scalarmult(self.B, a)
        return self.encodepoint(A)

    def signature(self,m,sk,pk):
        h = self.H(sk)
        a = 2**(self.n) + sum(2**i * self.bit(h,i) for i in range(self.c,self.n))
        r = self.Hint(h[self.b//8:self.b//4] + m)
        R = self.scalarmult(self.B,r)
        S = (r + self.Hint(self.encodepoint(R) + pk + m) * a) % self.l
        return self.encodepoint(R) + self.encodeint(S)

    def checkvalid(self,s,m,pk):
        if len(s) != self.b//4: raise Exception("signature length is wrong")
        if len(pk) != self.b//8: raise Exception("public-key length is wrong")
        R = self.decodepoint(s[0:self.b//8])
        A = self.decodepoint(pk)
        S = self.decodeint(s[self.b//8:self.b//4])
        h = self.Hint(self.encodepoint(R) + pk + m)
        if self.scalarmult(self.B,S) != self.edwards(R,self.scalarmult(A,h)):
            raise Exception("signature does not pass verification")


class Ed25519(EdDSA):
    q = 2**255 - 19
    b = 256
    n = 254
    c = 3
    l = 2**252 + 27742317777372353535851937790883648493
    B = (15112221349535400772501151409588531511454012693041857206046113283949847762202, 46316835694926478169428394003475163141307993866256225615783033603165251855960)
    d = -4513249062541557337682894930092624173785641285191125241628941591882900924598840740
    a = -1

    def __init__(self):
        self.I = pow(2, (self.q-1) // 4, self.q)

    def H(self, s):
        return bytearray(hashlib.sha512(s).digest())

    def xrecover(self, y):
        xx = (y*y-1) * self.inv(self.d*y*y+1)
        x = pow(xx,(self.q+3)//8,self.q)
        if (x*x - xx) % self.q != 0: x = (x*self.I) % self.q
        if x % 2 != 0: x = self.q-x
        return x


class Ed448(EdDSA):
    q = 2**448 - 2**224 - 1
    b = 456
    n = 447
    c = 2
    l = 2**446 - 13818066809895115352007386748515426880336692474882178609894547503885
    # https://tools.ietf.org/html/draft-irtf-cfrg-curves-07#section-4.2
    B = (224580040295924300187604334099896036246789641632564134246125461686950415467406032909029192869357953282578032075146446173674602635247710, 298819210078481492676017930443930673437544040154080242095928241372331506189835876003536878655418784733982303233503462500531545062832660)
    d = -39081
    a = 1

    def H(self, s):
        return CompactFIPS202.SHAKE256(bytearray(s), (self.b*2)//8)

    def xrecover(self, y):
        # special case since q == 3 (mod 4)
        x = pow(y, (self.q + 1)//4, self.q)
        if x % 2 != 0: x = self.q-x
        assert self.isoncurve((x,y))
        return x


def test():
    import binascii

    def DEC(s):
        return bytearray(binascii.unhexlify(s))

    e = Ed25519()

    # test 1
    sk = DEC("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
    pk = e.publickey(sk)
    pk_ref = DEC("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
    assert pk == pk_ref
    m = DEC('')
    sig_ref = DEC("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
    sig = e.signature(m,sk,pk)
    assert sig == sig_ref
    e.checkvalid(sig, m, pk)

    # test 2
    sk = DEC("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb")
    pk = e.publickey(sk)
    pk_ref = DEC("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")
    assert pk == pk_ref
    m = DEC("72")
    sig_ref = DEC("92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00")
    sig = e.signature(m,sk,pk)
    assert sig == sig_ref
    e.checkvalid(sig, m, pk)

    print("potential test vectors for Ed448")
    print("SK: 9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
    e = Ed448()
    sk = DEC("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
    pk = e.publickey(sk)
    m = b''
    sig = e.signature(m,sk,pk)
    print("PK: " + binascii.hexlify(pk).decode('ascii'))
    print("SIG: " + binascii.hexlify(sig).decode('ascii'))


test()
