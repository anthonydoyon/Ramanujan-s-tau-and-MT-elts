︠a75283db-4161-4bf4-9572-41fde381db73︠
#Code for computing Iwasawa-invariants of Mazur-Tate elements and potential reduction of elliptic curves over Q
#By Anthony Doyon and Antonio Lei
#Linked article: Congruences between Ramanujan's tau function and elliptic curves, and Mazur-Tate elements at additive primes

#Some interesting remarks concerning the following code:
#For further theoretical discussions about p-adic Mazur-Tate elements, we suggest the reader to consult Pollack and Weston's 2009 article named
#Mazur-Tate elements of non-ordinary modular forms. The computations we carry in this program compute the p-adic Mazur-Tate elements associated
#to a modular form theta_n,i as in PW 2009 but only for i=0. Some slight modifications to this code would allow the computation of theta_n,i for
#0 \leq i \leq p-2.

def mt_ec(E,p,n):
    """
    Returns the Mazur-Tate element theta_n for a prime p as in Pollack-Weston 2009.
    Input:
    E -- An elliptic curve
    p -- An odd prime
    n -- The level (>=1) of the Mazur-Tate element computed
    Output:
    A list where each element represents a permutation and its associated coefficient. Each element of the list has the form [b,coeff_b] where
    0 < b < p^(n+1) is an integer used to represent the permutation sigma_b in G_n+1 := Gal(Q(mu_p^(n+1))/Q) which acts as follows on a primitive
    p^(n+1)th root of unity zeta : sigma_b(zeta) = zeta^b. Coeff_b is the coefficient associated to the permutation represented by b i.e.
    phi([oo] - [b/p^(n+1)])|(X,Y)=(0,1) where phi is the modular symbol associated to E. theta_n in Z[G_n+1] is simply the sum of all coeff_b * sigma_b
    for all b not congruent to 0 mod p. For a more detailed discussion, we invite the reader to consult Pollack-Weston 2009 section 2.
    """
    phi = E.modular_symbol(sign=1)
    deno = []
    ans = []
    for b in range(p^(n+1)):
        if b % p == 0:
            pass
        else:
            deno.append(phi(b/(p^(n+1))).as_integer_ratio()[1])
            ans.append([b,phi(b/(p^(n+1)))])
    #We then normalise the coefficients so that they lie in Z and have no common factor. This normalization might not correspond to dividing by the
    #cohomological period as in PW 2009 (definition 2.1) but it is used to make sure that mu = 0 which is the case of interest.
    scalefact = lcm(deno)
    coeff_list = []
    for elt in ans:
        elt[1] *= scalefact
        coeff_list.append(elt[1])
    if gcd(coeff_list) == 1 or gcd(coeff_list) == 0:
        pass
    else:
        for elt in ans:
            elt[1] /= gcd(coeff_list)
    return ans

def mod_symb_delta(r1,r2):
    """
    Computes the modular symbol of sign +1 of delta in S_12(SL2Z) and evaluates phi([r1,r2]).
    """
    M = ModularSymbols(SL2Z,12,1).cuspidal_subspace()
    w=M.dual_eigenvector()
    M=M.ambient_module()
    return w.dot_product(M.modular_symbol([r1,r2]).element())

def mt_delta(p,n):
    """
    Returns the p-adic Mazur-Tate element for delta theta_n. Functions the same as mt_ec() but the modular symbol of sign +1
    of E is replaced by the modular symbol associated to delta computed with mod_symb_delta().
    """
    ans = []
    deno = []
    for b in range(p^(n+1)):
        if b % p == 0:
            pass
        else:
            deno.append(mod_symb_delta(oo, b/(p^(n+1))).as_integer_ratio()[1])
            ans.append([b,mod_symb_delta(oo, b/(p^(n+1)))])
    scalefact = lcm(deno)
    coeff_list = []
    for elt in ans:
        elt[1] *= scalefact
        coeff_list.append(elt[1])
    if gcd(coeff_list) == 1:
        pass
    else:
        for elt in ans:
            elt[1] /= gcd(coeff_list)
    return ans

def mt_to_poly(mt,p,n):
    """
    Transforms a Mazur-Tate element theta_n to a polynomial in order to compute its Iwasawa-invariants.
    Input:
    mt -- A Mazur-Tate element theta_n as outputed by mt_ec() or mt_delta()
    p -- An odd prime
    n -- The level of the Mazur-Tate element mt
    Output:
    Let Lambda be the Iwasawa algebra obtained by taking the projective limit over n of Z_p[G_n] where G_n =  Gal(Q(mu_p^(n+1))/Q).
    We fix an isomorphism Lambda \cong Z_p[t]. Then, this function outputs a polynomial representing the projection of mt in Lambda/((1+t)^(p^n) - 1).
    When p = 2, the calculations are a bit different (see our linked article for more details).
    """
    R,t = QQ['t'].objgen()
    poly_list = []
    poly = 0

    if p == 2:
        for elt in mt:
            i = 0
            while i <= p^(n-1):
                if (5^i % p^(n+1) == elt[0] % p^(n+1)) or (-5^i % p^(n+1) == elt[0] % p^(n+1)):
                    poly += elt[1]*(1+t)^i
                    break
                i += 1
    else:
        for elt in mt:
            omega_elt = list(Zp(p,10).teichmuller(elt[0]).expansion())
            omega = omega_elt[0]
            poly_list.append([elt[0]*omega.inverse_mod(p^(n+1)), elt[1]])
        for elt in poly_list:
            temp = True
            m = 0
            while temp:
                if (1+p)^m % p^(n+1) == elt[0] % p^(n+1):
                    temp = False
                else:
                    m += 1
            poly += elt[1]*(1+t)^m
    return poly

def mu_inv(poly,p):
    """
    Returns the Iwasawa mu-invariant for p of a polynomial.
    """
    if poly == 0:
        return oo
    else:
        return min([poly[a].valuation(p) for a in range(poly.degree()+1)])

def lambda_inv_ord(poly,p):
    """
    Returns the Iwasawa lambda-invariant for p of a polynomial associated to an elliptic curve having good ordinary reduction at p.
    This algorithm differs from the ones currently used because most of our computations are done for polynomials of mu-invariant = 0.
    """
    m = mu_inv(poly,p)
    if poly == 0:
        return oo
    elif poly.degree() < 20:
        v = [poly[a].valuation(p) for a in range(poly.degree() + 1)]
        return v.index(m)
    else:
        coeff = poly.list()[0:21]
        while True:                                  #We expect lambda to be quite small, so we are not interested in the higher order terms.
            if all(x % p == 0 for x in coeff):       #Once we got rid of these terms, we renormalize our polynomial so that its mu-invariant = 0
                coeff[:] = [x / p for x in coeff]    #and then compute its lambda-invariant.
            else:
                break
        for i in range(21):
            if coeff[i].valuation(p) == m:
                return i
            else:
                pass

def q_n(p,n):
    """
    Computes an error term involved in the calculation of the lambda-invariant of elliptic curves with supersingular reduction at p.
    Input:
    p -- An odd prime
    n -- A positive integer
    Output:
    The supersingular error term q_p,n defined as in Pollack-Weston 2009 section 1.
    """
    ans = 0
    if n % 2 == 0:
        for i in range(n):
            ans += (-1)^(i+1)*p^i
    else:
        for i in range(1,n):
            ans += (-p)^i
    return ans

def lambda_inv_ss(poly,p,n):
    """
    Returns the lambda^+/- of a polynomial poly associated to Pollack's L_p^+/- depending on the parity of n. Here, n is the level of the
    p-adic Mazur-Tate element associated to poly. See section 1 of Pollack and Weston's 2009 article for further discussions on the p-adic
    Iwasawa lambda^+/- invariants.
    """
    if poly == 0:
        return oo
    else:
        m = mu_inv(poly,p)
        coeff = poly.list()[0:poly.degree() + 1]
        for i in range(len(coeff)):
            if coeff[i].valuation(p) == m:
                lambda_mt = i
                break
            else:
                pass
        if p == 2:
            lambda_plus_minus = lambda_mt - q_n(p,n-1)
        else:
            lambda_plus_minus = lambda_mt - q_n(p,n)
    return lambda_plus_minus

def lambda_inv(poly,p):
    """
    Returns the p-adic lambda-invariant of a polynomial.
    """
    if poly == 0:
        return oo

    else:
        coeff = poly.list()
        while True:
            if all(x % p == 0 for x in coeff):
                coeff[:] = [x / p for x in coeff]
            else:
                break
        for i in range(len(coeff) + 1):
            if coeff[i].valuation(p) == 0:
                return i
            else:
                pass

def data_ec(E,p,n):
    """
    Prints data about the p-adic Mazur-Tate elements theta_n of an elliptic curve of mu = 0 in the isogeny class of E.
    """
    print "Elliptic curve in the isogeny class  " + str(E.isogeny_class())
    print E.local_data(p)
    print "Mazur-Tate element of level " + str(n) + ":"
    mt = mt_ec(E,p,n)
    print mt
    print
    print "Polynomial associated to theta_" + str(n) + " :"
    poly = mt_to_poly(mt,p,n)
    print poly
    print
    if E.is_ordinary(p):
        if p == 2:
            print "Not implemented yet"
        else:
            print "Lambda-invariant: " + str(lambda_inv_ord(poly,p))
            print "Mu-invariant: " + str(mu_inv(poly,p))
            print
    elif E.is_supersingular(p):
        if (n + 1) % 2 == 0:
            print "Lambda^+: " + str(lambda_inv_ss(poly,p,n))
            print "Mu^+: " + str(mu_inv(poly,p))
            print
        else:
            print "Lambda^-: " + str(lambda_inv_ss(poly,p,n))
            print "Mu^-: " + str(mu_inv(poly,p))
            print
    else:
        print "Lambda: " + str(lambda_inv(poly,p))
        print "Mu: " + str(mu_inv(poly,p))
        print

def data_delta(p,n):
    """
    Prints data about the p-adic Mazur-Tate elements theta_n of Ramanujan's tau function.
    """
    print "Mazur-Tate element of level " + str(n) + ":"
    mt = mt_delta(p,n)
    print mt
    print
    print "Polynomial associated to theta_" + str(n) + " :"
    poly = mt_to_poly(mt,p,n)
    print poly
    print
    print "Lambda-invariant: " + str(lambda_inv(poly,p))
    print "Mu-invariant: " + str(mu_inv(poly,p))

def pot_red(E,p):
    """
    Returns data concerning the potential reduction at p of an elliptic curve E having additive reduction at p.
    Input:
    E -- An elliptic curve (over Q)
    p -- A prime
    Output:
    A tuple (K, red) where K is a finite extension of Q where E attains a non-additive reduction red.
    """
    R,t = QQ['t'].objgen()
    i = 0
    done = False
    list_deg = [2, 3, 4, 6, 12]
    while not(done) and i <= 4:
        m = list_deg[i]
        n = 0
        while n <= 12:
            n += 1
            if (t^m - n*p).is_irreducible():
                K = NumberField(x^m - n*p, "a")
                J = K.ideal(p).factor()[0][0]
                F = E.base_extend(K)
                if not(F.has_additive_reduction(J)):
                    if F.has_split_multiplicative_reduction(J):
                        red = "split multiplicative"
                    elif F.has_nonsplit_multiplicative_reduction(J):
                        red = "non-split multiplicative"
                    elif F.reduction(J).is_ordinary(J):
                        red = "good ordinary"
                    else:
                        red = "supersingular"
                    done = True
                    break
        i += 1
    print F.local_data(J)
    return (K, red)

#Calculation of the lambda-invariant of a p-adic Mazur-Tate element of level n associated to an elliptic curve
#p = 3
#n = 3
#E = CremonaDatabase().elliptic_curve("27a1")
#data_ec(E,p,n)

#Calculation of the lambda-invariant of a p-adic Mazur-Tate element of level n associated to Delta
#p = 3
#n = 3
#data_delta(p,n)

#Calculation of the potential reduction of an elliptic curve
#print pot_red(E,p)









