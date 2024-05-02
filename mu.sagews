#This code is used in the computations of the p-adic mu-invariants for Delta
#Linked article: Lambda-invariants of Mazur-Tate elements attached to Ramanujan's tau function and congruences with Eisenstein series
#The authors thank Robert Pollack who sent us the following code that we adapted to our computations.

#This code is used to compute the cohomological period and normalize suitably the modular symbol attached to Delta allowing us to get results on the Iwasawa mu-invariant of these symbols.
M = ModularSymbols(1,12,1).cuspidal_subspace()
w = M.dual_eigenvector()
M = M.ambient_module()
p = 3                     # The primes p of interest to us are 3, 5 and 7.
n = 1

print("My calculations for p = " + str(p) + ": ")
v=list(Gamma1(p^n).coset_reps())
for g in v:
    print()
    print("Coset representative: \n" + str(g))
    if g[1][0] == 0:
        print("p-valuations: " + str([w.dot_product(M.modular_symbol([j,Infinity,g[0][1]/g[1][1]]).element()).valuation(p)+binomial(10,j).valuation(p) for j in range(0,11,2)]))            #Computes the p-valuation of the modular symbols associated to Delta against every coset representative of Gamma_1(p^n).
    elif g[1][1] == 0:
        print("p-valuations: " + str([w.dot_product(M.modular_symbol([j,g[0][0]/g[1][0],Infinity]).element()).valuation(p)+binomial(10,j).valuation(p) for j in range(0,11,2)]))
    else:
        print("p-valuations: " + str([w.dot_product(M.modular_symbol([j,g[0][0]/g[1][0],g[0][1]/g[1][1]]).element()).valuation(p)+binomial(10,j).valuation(p) for j in range(0,11,2)]))
