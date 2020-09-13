︠a75283db-4161-4bf4-9572-41fde381db73s︠
#Code for computing Iwasawa-invariants of Mazur-Tate elements and potential reduction of elliptic curves over Q
#By Anthony Doyon and Antonio Lei

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
    for all b not congruent to 0 mod p.
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
    #We then normalise the coefficients so that they lie in Z and have no common factor.
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
        if b % p ==0:
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
    """
    R,t = QQ['t'].objgen()
    poly_list = []
    poly = 0

    for elt in mt:
        omega_elt = list(Zp(p,10).teichmuller(elt[0]).expansion())
        omega = omega_elt[0]
        poly_list.append([elt[0]*omega.inverse_mod(p^n), elt[1]])

    for elt in poly_list:
        temp = True
        m = 0
        while temp:
            if (1+p)^m % p^n == elt[0] % p^n:
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
        while True:
            if all(x % p == 0 for x in coeff):
                coeff[:] = [x / p for x in coeff]
            else:
                break
        for i in range (len(coeff)):
            if coeff[i].valuation(p) == m:
                lambda_mt = i
                break
            else:
                pass
        lambda_plus_minus = lambda_mt - q_n(p,n)
    return lambda_plus_minus

def lambda_inv(poly,p):
    """
    Returns the p-adic lambda-invariant of a polynomial.
    """
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
    poly = mt_to_poly(mt,p,n+1)
    print poly
    print
    if E.is_ordinary(p):
        print "Lambda-invariant: " + str(lambda_inv_ord(poly,p))
        print "Mu-invariant: " + "0"
    elif E.is_supersingular(p):
        if (n + 1) % 2 == 0:
            print "Lambda^+: " + str(lambda_inv_ss(poly,p,n))
            print "Mu^+: 0"
        else:
            print "Lambda^-: " + str(lambda_inv_ss(poly,p,n))
            print "Mu^-: 0"
    else:
        print "Lambda: " + str(lambda_inv(poly,p))
        print "Mu: 0"

def data_delta(p,n):
    """
    Prints data about the p-adic Mazur-Tate elements theta_n of Ramanujan's tau function.
    """
    print "Mazur-Tate element of level " + str(n) + ":"
    mt = mt_delta(p,n)
    print mt
    print
    print "Polynomial associated to theta_" + str(n) + " :"
    poly = mt_to_poly(mt,p,n+1)
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
        while n <= 49:
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

#Example of calculations
p = 3
E = CremonaDatabase().elliptic_curve("37a1")
#print pot_red(E,p)

data_ec(E,p,4)
#data_delta(p,4)
︡3251585c-7fe3-43ba-a830-ef95115642f9︡{"stdout":"Elliptic curve in the isogeny class  Elliptic curve isogeny class 37a\nLocal data at Principal ideal (3) of Integer Ring:\nReduction type: good\nLocal minimal model: Elliptic Curve defined by y^2 + y = x^3 - x over Rational Field\nMinimal discriminant valuation: 0\nConductor exponent: 0\nKodaira Symbol: I0\nTamagawa Number: 1\nMazur-Tate element of level 4:\n[[1, -1], [2, 0], [4, 0], [5, 1], [7, -1], [8, 0], [10, -1], [11, -1], [13, 1], [14, 0], [16, 0], [17, 0], [19, -1], [20, 0], [22, 0], [23, 0], [25, -2], [26, 0], [28, 1], [29, 0], [31, 2], [32, 1], [34, 0], [35, 1], [37, 1], [38, 0], [40, 1], [41, 0], [43, 1], [44, 1], [46, 1], [47, -1], [49, 1], [50, 3], [52, 1], [53, 2], [55, 0], [56, 0], [58, 0], [59, 0], [61, 0], [62, 0], [64, 0], [65, -1], [67, 0], [68, 1], [70, 0], [71, -1], [73, 0], [74, 0], [76, 1], [77, 0], [79, 1], [80, -1], [82, -1], [83, 0], [85, -1], [86, 0], [88, -1], [89, 0], [91, -1], [92, -1], [94, 0], [95, -1], [97, -1], [98, 0], [100, -2], [101, 1], [103, -1], [104, -1], [106, -3], [107, 0], [109, 0], [110, 0], [112, 0], [113, 0], [115, -1], [116, 1], [118, 1], [119, 0], [121, 1], [122, 1], [124, 0], [125, 1], [127, 1], [128, -1], [130, 0], [131, 0], [133, 0], [134, 0], [136, 0], [137, -3], [139, -1], [140, -1], [142, 1], [143, -2], [145, 0], [146, -1], [148, -1], [149, 0], [151, -1], [152, -1], [154, 0], [155, -1], [157, 0], [158, -1], [160, 0], [161, -1], [163, -1], [164, 1], [166, 0], [167, 1], [169, 0], [170, 0], [172, -1], [173, 0], [175, 1], [176, 0], [178, -1], [179, 0], [181, 0], [182, 0], [184, 0], [185, 0], [187, 0], [188, 0], [190, 2], [191, 1], [193, 3], [194, 1], [196, -1], [197, 1], [199, 1], [200, 1], [202, 0], [203, 1], [205, 0], [206, 1], [208, 1], [209, 0], [211, 1], [212, 2], [214, 0], [215, 1], [217, 0], [218, -2], [220, 0], [221, 0], [223, 0], [224, -1], [226, 0], [227, 0], [229, 0], [230, 1], [232, -1], [233, -1], [235, 0], [236, -1], [238, 1], [239, 0], [241, 0], [242, -1]]\n\nPolynomial associated to theta_4 :\nt^80 + 80*t^79 + 3159*t^78 + 82082*t^77 + 1578578*t^76 + 23964016*t^75 + 299076624*t^74 + 3155675537*t^73 + 28731965902*t^72 + 229276807723*t^71 + 1623262759245*t^70 + 10297483598600*t^69 + 59007012754709*t^68 + 307498442994706*t^67 + 1465662337376291*t^66 + 6421004088817149*t^65 + 25964890797838877*t^64 + 97271015576246982*t^63 + 338684352795401165*t^62 + 1099149508086944217*t^61 + 3333207772406109836*t^60 + 9466399183194091240*t^59 + 25228529318462955916*t^58 + 63206242848094415153*t^57 + 149102355211140317650*t^56 + 331657303825036711318*t^55 + 696522813926418587578*t^54 + 1382689318437272153460*t^53 + 2597216443277265422430*t^52 + 4620504455570116475314*t^51 + 7791630876890423595380*t^50 + 12463642958055051510019*t^49 + 18924392947138320478229*t^48 + 27290222203318224935237*t^47 + 37395156039890259898626*t^46 + 48711406020699006346087*t^45 + 60340256305433711763934*t^44 + 71100116390160523077494*t^43 + 79710933135996252364822*t^42 + 85039462132433023575660*t^41 + 86341982932081665686977*t^40 + 83433362298795160858034*t^39 + 76729856943813209214449*t^38 + 67152125942069003067388*t^37 + 55919374711682891354456*t^36 + 44297608997220499376656*t^35 + 33372812055324078442478*t^34 + 23902782585131237304843*t^33 + 16269107290698788150680*t^32 + 10517702917342882390244*t^31 + 6454546350557197291012*t^30 + 3757547213805444407377*t^29 + 2073482473936586871364*t^28 + 1083601811368169055204*t^27 + 535767983034657609402*t^26 + 250338638903907002948*t^25 + 110398881572053354149*t^24 + 45883377687618365439*t^23 + 17942572933012422852*t^22 + 6589330696567478397*t^21 + 2267786230212882366*t^20 + 729647405672099826*t^19 + 218858870906174862*t^18 + 61003917529895781*t^17 + 15742227793918401*t^16 + 3744343543385430*t^15 + 816598268322369*t^14 + 162260710839186*t^13 + 29147855179560*t^12 + 4687382518530*t^11 + 666299303784*t^10 + 82299360381*t^9 + 8620694577*t^8 + 737397075*t^7 + 48097260*t^6 + 2010672*t^5 + 10269*t^4 - 5733*t^3 - 486*t^2 - 18*t\n\nLambda^-: 5\nMu^-: 0\n"}︡{"done":true}









