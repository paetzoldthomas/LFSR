from operator import itemgetter
from itertools import combinations
import random
import sys

from sage.crypto.boolean_function import BooleanFunction
from sage.geometry.hyperplane_arrangement.affine_subspace import AffineSubspace

class LFSR:
    _base_ring = None
    _degree = 0
    _fb_poly = None
    _fb_poly_ = None
    _state = None
    _companion_matrix = None

    _f_small = None
    _f_big1 = None
    _f_big2 = None

    def __init__(self, R, feedback_poly, initial_state_as_int):
        """
        Creates an LFSR with initial state, which is represented by its companion matrix
        """
        self._base_ring = R
        self._degree = feedback_poly.degree()
        self._fb_poly = vector(self._base_ring, [i for i in feedback_poly])
        self._fb_poly_ = feedback_poly
        self._state = self.int2vec(initial_state_as_int)

        R3 = BooleanPolynomialRing(n=3, names="x")
        self._f_small = BooleanFunction(R3("x0*x1 + x2"))

        R6 = BooleanPolynomialRing(n=6, names="x")
        self._f_big1 = BooleanFunction(R6("x0*x1*x2*x3*x4 + x0*x1*x2*x3*x5 + x0*x1*x2*x3 + x0*x1*x2*x4*x5 + x0*x1*x2*x4 + x0*x1*x2 + x0*x1*x3*x4*x5 + x0*x1*x3 + x0*x1*x4 + x0*x1*x5 + x0*x2*x3*x4*x5 + x0*x2*x3*x4 + x0*x2*x3 + x0*x2*x4*x5 + x0*x2 + x0*x3*x4*x5 + x0*x3*x4 + x0*x4 + x0*x5 + x0 + x1*x2*x3*x4*x5 + x1*x2*x3 + x1*x2*x4 + x1*x2*x5 + x1*x2 + x1*x3*x4*x5 + x1*x3*x4 + x1*x3*x5 + x1*x3 + x1 + x2*x3 + x2*x4*x5 + x2 + x3 + x4*x5 + x4 + 1"))
        self._f_big2 = BooleanFunction(R6("x0*x1*x2*x3*x4*x5 + x0*x1*x2*x3*x4 + x0*x1*x2*x3 + x0*x1*x2*x4 + x0*x1*x3*x4*x5 + x0*x1*x4*x5 + x0*x1*x4 + x0*x1*x5 + x0*x2*x3*x4 + x0*x2*x3*x5 + x0*x2*x3 + x0*x2*x4 + x0*x3*x4*x5 + x0*x3*x4 + x0*x3*x5 + x0*x3 + x0*x4 + x0*x5 + x0 + x1*x2*x3*x4*x5 + x1*x2*x3*x4 + x1*x2*x4 + x1*x2*x5 + x1*x3 + x1*x4*x5 + x1*x4 + x1*x5 + x1 + x2*x3*x4*x5 + x2*x3*x5 + x2*x3 + x2*x4*x5 + x2*x4 + x2*x5 + x2 + x3*x4*x5"))

        self._companion_matrix = companion_matrix(self._fb_poly_, format="bottom")

    def __call__(self, filter_func='none'):
        """
        compute the output of the LFSR and clock it once
        """
        if filter_func is 'none':
            output = self._state[-1]
            self._state = self._companion_matrix * self._state
            return output
        elif filter_func is 'small':
            x0 = self._state[0]
            x1 = self._state[self._degree//2]
            x2 = self._state[self._degree-1]
            self._state = self._companion_matrix * self._state
            return 1 if self._f_small([x0, x1, x2]) else 0
        elif filter_func is 'big1':
            x0 = self._state[0]
            x1 = self._state[self._degree//4]
            x2 = self._state[self._degree//4 + self._degree//8]
            x3 = self._state[self._degree//2]
            x4 = self._state[self._degree//2 + self._degree//4]
            x5 = self._state[self._degree-1]
            self._state = self._companion_matrix * self._state
            return 1 if self._f_big1([x0, x1, x2, x3, x4, x5]) else 0
        elif filter_func is 'big2':
            x0 = self._state[0]
            x1 = self._state[self._degree//4]
            x2 = self._state[self._degree//4 + self._degree//8]
            x3 = self._state[self._degree//2]
            x4 = self._state[self._degree//2 + self._degree//4]
            x5 = self._state[self._degree-1]
            self._state = self._companion_matrix * self._state
            return 1 if self._f_big2([x0, x1, x2, x3, x4, x5]) else 0

    def __str__(self):
        """
        the string that is printed in print statements
        """
        return "LFSR with feedback polynomial 0x%x and state 0x%x" % \
            (self.vec2int(self._fb_poly), self.vec2int(self._state))

    def __repr__(self):
        """
        the string that is printed in interactive sessions
        """
        return "%s" % self

    def get_companion_matrix(self):
        """
        returns the matrix representation of the LFSR
        that is the companion matrix/multiplication of x in R/p
        """
        return self._companion_matrix

    def int2vec(self, x):
        """
        Returns the representation of x as vector over R, when interpreting each bit of
        x as an element of the vector
        """
        binlen_x = len(bin(x)[2:])
        xcoeff = ("0"*(self._degree - binlen_x) + bin(x)[2:])[::-1]
        return vector(self._base_ring, [ai for ai in xcoeff])[:self._degree]

    def vec2int(self, p):
        """
        inverse of int2vec
        """
        x = 0
        for e, p_i in enumerate([Integer(i) for i in p]):
            x += (p_i << e)
        return x

    def vec2mult_var_poly(self, v):
        """
        returns v as a multivariate polynomial
        """
        m = self._degree
        unkowns = ["x%d" % i for i in range(m)]
        Fx = BooleanPolynomialRing(names=unkowns)
        if len(v) > m:
            print("Oops, vector is longer than lfsr state, will truncate most significant elements")
            v = v[0:m]
        return Fx("+".join([unkowns[i] for i in range(m) if v[i] == 1]))

    def seed(self, x):
        """
        resets the initial state to x, where x is some integer
        """
        self._state = self.int2vec(x)

    def gen_tuples(self, setsize, maximalclocks, filter_func='None'):
        """
        generates a set S that is passed to aufgabeX
        """
        # generate maximalclocks many output bits and reset state afterwards
        setsize = setsize % maximalclocks
        backup_state = self._state
        raw_outputs = [(clock, self(filter_func)) for clock in range(maximalclocks)]
        self._state = backup_state

        # draw setsize many elements from raw_output and sort them
        outputs = random.sample(raw_outputs, setsize)
        outputs.sort(key=itemgetter(0))
        return outputs

class PARAMS:
    aufgabe3_1 = [1 << i for i in range(2, 10)]
    #aufgabe3_2 = load("lfsr_params_aufgabe3_2") # Dictionary {"polynomial": poly, "output": 2D-list}
    aufgabe4_1 = load("lfsr_params_aufgabe4_1") # Dictionary {"polynomial": poly, "output": 2D-list}
    aufgabe4_2 = load("lfsr_params_aufgabe4_2") # Dictionary {"polynomial": poly, "output": 3D-list}
    aufgabe4_3 = load("lfsr_params_aufgabe4_3") # Dictionary {"polynomial": poly, "output": 3D-list}


def aufgabe3_1(n):
    """
    On input n return an LFSR with maximal period and some random initial state
    """
    F = FiniteField(2)
    p = PolynomialRing(F, name="x").irreducible_element(n, algorithm="primitive")
    return LFSR(F, p, randint(0, 1<<n))


def aufgabe3_2(lfsr, S):
    """
    given an lfsr and a set S of tuples (i, s_i), s.t. the i'th output of the lfsr with
    unknown initial state x is s_i, return a basis of the set of all possible initial
    states X = {x_j}. Thus each possible initial state s is representable as a linear
    combination of the x_j.

    Hint: If your solution looks somewhat "special" in hex, you probably got the
    correct solution.
    """
    pass


def aufgabe4_1(lfsr, Z):
    """
    given an lfsr, assume that the corresponding filter function f is the same as in the
    lecture, thus f(x_1, x_2, x_3) = x_1 x_2 + x_3, and a set Z of tuples (z_i, i) (s.t.
    the same as for aufgabe2 holds), return a basis of the set of all possible initial
    states (thus use the same representation as in aufgabe2), by applying the technique
    of linearisation.
    """
    # TODO
    pass


def aufgabe4_2(lfsr, Zk, i):
    """
    Wie oben nur dieses Mal durch ausnutzen eines Annihilator.
    Der Parameter i gibt an, ob f_big1 oder f_big2 verwendet wird.
    """
    if i == 1:
        # f_big1 wurde verwendet
        # TODO
        pass
    elif i == 2:
        # f_big1 wurde verwendet
        # TODO
        pass
    else:
        print("wrong value for i parameter")


def solutiondict2vec(d):
    sol = list(d.iteritems())
    sol.sort(key=itemgetter(0), reverse=True)
    sol = list(map(itemgetter(1), sol))
    return sol


def aufgabe4_3(lfsr, Z):
    """
    the same as aufgabe4_1 but with Groebnerbases
    """
    # TODO
    pass


def check_students_solution():
    PARAMS.aufgabe3_1 = [1 << i for i in range(2, 10)]
    #PARAMS.aufgabe3_2 = load("lfsr_params_aufgabe3_2") # Dictionary {"polynomial": poly, "output": 2D-list}
    PARAMS.aufgabe4_1 = load("lfsr_params_aufgabe4_1") # Dictionary {"polynomial": poly, "output": 2D-list}
    PARAMS.aufgabe4_2 = load("lfsr_params_aufgabe4_2") # Dictionary {"polynomial": poly, "output": 3D-list}
    PARAMS.aufgabe4_3 = load("lfsr_params_aufgabe4_3") # Dictionary {"polynomial": poly, "output": 3D-list}
    #lfsr = LFSR(FiniteField(2), PARAMS.aufgabe3_2["polynomial"], 1) # initial state is irrelevant
    #for Z in PARAMS.aufgabe3_2["output"]:
    #    print(lfsr, aufgabe3_2(lfsr, Z))

    lfsr = LFSR(FiniteField(2), PARAMS.aufgabe4_1["polynomial"], 1) # initial state is irrelevant
    import time
    for Z in PARAMS.aufgabe4_1["output"]:
        before = time.clock()
        init_states = aufgabe4_1(lfsr, Z)
        print("%s seconds" % (time.clock()-before), init_states)

    lfsr = LFSR(FiniteField(2), PARAMS.aufgabe4_2["polynomial"], 1) # initial state is irrelevant
    for i, aufgabe4_2i in enumerate(PARAMS.aufgabe4_2["output"], 1):
        for Z in aufgabe4_2i:
            before = time.clock()
            init_states = aufgabe4_2(lfsr, Z, i)
            print("%s seconds" % (time.clock()-before), init_states)

    lfsr = LFSR(FiniteField(2), PARAMS.aufgabe4_3["polynomial"], 1) # initial state is irrelevant
    for Z in PARAMS.aufgabe4_3["output"]:
        before = time.clock()
        init_states = aufgabe4_3(lfsr, Z)
        print("%s seconds" % (time.clock()-before), init_states)

if __name__ == "__main__":
    check_students_solution()
