#Code for computing the Iwasawa p-adic lambda-invariants associated to Mazur-Tate elements of the Ramanujan's Delta function when p=3,5 or 7.
#By Anthony Doyon and Antonio Lei.
#Linked article: Lambda-invariants of Mazur-Tate elements attached to Ramanujan's tau function and congruences with Eisenstein series.
#Software: Sagemath v9.6

set_modsym_print_mode('modular')

def modsymbdelta(r1, r2):
    """
    Computes the modular symbol of sign +1 of delta in S_12(SL2Z) and evaluates it on the divisor {r1} - {r2}.
    """
    M = ModularSymbols(SL2Z,12,1).cuspidal_subspace()
    w=M.dual_eigenvector()
    M=M.ambient_module()
    return w.dot_product(M.modular_symbol([r2,r1]).element())

def data_modsym_gens(N):
    """
    Prints a list of divisors that completely determine the image of a modular symbol of weight two for Gamma1(N) with values in any coefficient module.
    This function is used in the calculations for the proof of Theorem 3.8 and Theorem 3.10.
    This function essentially uses the implementation of modular symbols of William Stein. From Stein's point of view, modular symbols lie in the homology
    of the upper-half plane relative to cusps. Our point of view uses cohomology, so our definitions of modular symbols are duals of each other.

    Input: N -- an integer 5,7 or 27.
    """
    assert N == 5 or N == 7 or N == 27, "N must be either 5,7 or 27, got: N = " + str(N)
    if N == 5:
        print("S_5 = " + str(ModularSymbols(Gamma1(5), 2).basis()))
        print()
    elif N == 7:
        print("S_7 = " + str(ModularSymbols(Gamma1(7), 2).basis()))
        print()
    elif N == 27:
        print("S_27 = " + str(ModularSymbols(Gamma1(27), 2).basis()))
        print()

def modsym_gens(N):
    """
    Input: N -- an integer 5,7 or 27

    Output: List -- The list S_N printed by the function data_modsym_gens(N) in the following format [(a_1, b_1), (a_2, b_2), ...] where
    {a_n} -  {b_n} are the divisors in S_N.
    """
    assert N == 5 or N == 7 or N == 27, "N must be either 5,7 or 27, got: N = " + str(N)
    if N == 5:
        return [(-2/5, -1/3), (1/5, 1/4), (-1/3, -1/4)]
    if N == 7:
        return [(-2/7, -1/4), (-3/7, -2/5), (1/7, 1/6), (4/25, 1/6), (-1/5, -1/6)]
    if N == 27:
        return [(-2/27, -1/14), (5/27, 3/16), (-8/27, -5/17), (-10/27, -7/19), (4/27, 3/20), (11/27, 9/22), (7/27, 6/23), (-2/9, -5/23), (-3/17, -4/23), (7/18, 9/23), (-5/19, -6/23),     (-12/41, -7/24), (-9/43, -5/24), (-5/17, -7/24), (-4/19, -5/24), (-2/47, -1/24), (-13/27, -12/25), (-9/32, -7/25), (-1/6, -4/25), (-2/7, -7/25), (-4/9, -11/25), (-3/37, -2/25), (-4/11, -9/25), (5/14, 9/25), (5/42, 3/25), (7/16, 11/25), (5/18, 7/25), (3/19, 4/25), (15/47, 8/25), (5/21, 6/25), (7/22, 8/25), (11/23, 12/25), (1/27, 1/26), (1/3, 9/26), (-41/355, -3/26), (-1/5, -5/26), (151/357, 11/26), (-3/7, -11/26), (69/359, 5/26), (1/9, 3/26), (-125/361, -9/26), (-3/11, -7/26), (-14/363, -1/26), (14/365, 1/26), (4/15, 7/26), (127/367, 9/26), (-2/17, -3/26), (-71/369, -5/26), (8/19, 11/26), (-157/371, -11/26), (4/21, 5/26), (43/373, 3/26), (-8/23, -9/26), (-101/375, -7/26), (-1/25, -1/26)]

def phi(N,D):
    """
    Computes the values of the boundary symbols appearing in Theorem 3.7 and Theorem 3.8.
    """
    assert N == 5 or N == 7 or N == 9, "N must be either 5,7 or 9, got: N = " + str(N)
    if N == 5:
        dict5 = {"0" : 0, "2/5" : 3, "1/2" : 0, "Infinity" : 2}
        return(dict5[str(Gamma1(5).reduce_cusp(D))])
    if N == 7:
        dict7 = {"0" : 0, "2/7" : 1, "1/3" : 0, "3/7" : 4, "1/2" : 0, "Infinity" : 2}
        return(dict7[str(Gamma1(7).reduce_cusp(D))])
    if N == 9:
        dict9 = {"0" : 1, "2/27" : 3, "1/13" : 7, "1/12" : 1, "1/11" : 4, "1/10" : 1, "1/9" : 0, "1/8" : 1, "1/7" : 4, "4/27" : 6 , "1/6" : 7, "5/27" : 6, "1/5" : 7, "2/9" : 3, "1/4" : 7, "7/27" : 3, "8/27" : 0, "1/3" : 4, "10/27" : 0, "11/27" : 3, "5/12" : 1, "4/9" : 6, "13/27" : 6, "1/2" : 4, "5/9" : 6, "2/3" : 4, "7/9" : 3, "5/6" : 7, "8/9" : 0, "Infinity" : 0}
        return(dict9[str(Gamma1(27).reduce_cusp(D))])

#Calculations of Theorem 3.8 for p = 5.
#We verify that the projection alpha_5 varphi_Delta^+ agrees modulo 5 with the reduction mod 5 of the Eisenstein boundary symbol in Theorem 3.8.
#To obtain 5-integral values for phi_Delta^+, one has to normalize it by 5 (see the discussion about the cohomological period).
#We have c_5 = 2.
print("Calculations of Theorem 3.8 for p = 5: ")
data_modsym_gens(5)
verif_list5 = [((modsymbdelta(elt[0], elt[1]) / 5) % 5) == (2 * (phi(5,elt[0]) - phi(5, elt[1]))) % 5 for elt in modsym_gens(5)]
print(all(verif_list5))
print()


#Calculations of Theorem 3.8 for p = 7.
#We verify that the projection alpha_7 varphi_Delta^+ agrees modulo 7 with the reduction mod 7 of the Eisenstein boundary symbol in Theorem 3.8.
#The values of phi_Delta^+ are already 7-integral so one does not need any further normalization (see the discussion about the cohomological period).
#We find c_7 = 1.
print("Calculations of Theorem 3.8 for p = 7: ")
data_modsym_gens(7)
verif_list7 = [(modsymbdelta(elt[0], elt[1]) % 7) == (phi(7,elt[0]) - phi(7, elt[1])) % 7 for elt in modsym_gens(7)]
print(all(verif_list7))
print()

#Calculations of Theorem 3.10 for p = 3.
#We verify that the projection alpha_9 varphi_Delta^+ agrees modulo 9 with the reduction mod 9 of the boundary symbol in Theorem 3.10.
#To obtain 3-integral values for phi_Delta^+, one has to normalize it by 81 (see the discussion about the cohomological period).
print("Calculations of Theorem 3.10 for p = 3: ")
data_modsym_gens(27)
verif_list9 = [((modsymbdelta(elt[0], elt[1]) / 81) % 9) == (phi(9,elt[0]) - phi(9, elt[1])) % 9 for elt in modsym_gens(27)]
print(all(verif_list9))
print()
