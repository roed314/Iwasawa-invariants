import time
from sage.databases.cremona import parse_cremona_label

def write_to_file(filename,line):
	"""
	Writes the string line to the file ``filename``.

	Input:

	-	``filename`` -- string
	-	``line`` -- string
	"""
	f = open(filename,'a')
	f.write(line)
	f.close()

def mu_bail(p):
	"""
	For a given prime p, returns the n for which we should keep trying to 
	compute Mazur-Tate elements to level p^n in hoping that their mu-invariants will vanish.
	The below values were just picked after a few trial runs.  In practice,
	mu should always eventually be zero (by how the code is normalized) and
	so these parameters are just setting how long we want to wait

	Input:

	-	``p`` -- prime
	"""
	if p<1000:
		return max(round(log(1000)/log(p)),4)-1
	else:
		return -1


def MazurTate(E,p,n,phi=None,twist=0,modp=false,logfile=None,bigcallfile=None,bigcall=infinity):
	"""
	Returns the p-adic Mazur-Tate element of level n.  That is, for p odd, we take the element

		sum_{a in (Z/p^{n+1}Z)^*} [a/p^{n+1}]^+_E sigma_a

	in Q[Gal(Q(mu_{p^{n+1}}))] and project it to Q[Gal(Q_n/Q)] where Q_n is the
	n-th level of the cyclotomic Z_p-extension.  The projection here is twisted by omega^twist so 
	that the group algebra element [a] maps to omega^twist(a)[a].
	(For p=2, one projects from level n+2, see Kurihara-Otsuki)

	Input:

	-	``E`` -- elliptic curve

	-	``p`` -- prime

	-	``n`` -- integer >= -1

	-	``phi`` -- None (default) or an order pair where phi[0] is the modular symbol attached
		to an elliptic curve in the isogeny class of E (typically chosen to minimize the mu-invariant
		in the isogeny class) and phi[1] is a constant used to rescale phi[0] (typically chosen to be
		1/(# of real components of E).  This ordered pair business can be dropped once SAGE's 
		normalization problems with modular symbols is fixed

	-	``twist`` -- 0 (default) or an integer between 0 and p-2 denoting the twist described above

	-	``logfile`` -- None (default) or string; if given then information about the computation is outputted
		to the file ``logfile``

	- 	``bigcallfile`` -- string (see below)

	-	``bigcall`` -- infinity (Default) or some real number.  When specified, writes info to bigcallfile
		if the call to this function makes longer than ``bigcall``
	"""
	if logfile != None:
		line = "   Computing Mazur-Tate at level "+str(n)+'\n'
		write_to_file(logfile,line)
	start = time.time()
	if phi == None:
		phi = (E.modular_symbol(),1/E.real_components())

	if modp and (p!=2):
		R.<T> = PolynomialRing(GF(p))
	else:
		R.<T> = PolynomialRing(QQ)
	if n == -1:
		ans = R(phi[0](0)*phi[1])
	else:
		mt = R(0)
		if p > 2:
			gam = 1+p
			Qp = pAdicField(p,2*n + 5)   ## should check carefully the accuracy needed here
			teich = Qp.teichmuller_system()
			teich = [0] + teich  ## makes teich[a] = omega(a)
			teich = [ZZ(teich[a]) for a in range(p)]
			gampow = 1 ## will make gampow = gam^pow
			oneplusTpow = 1 ## will make oneplusTpow = (1+T)^pow
			for j in range(p^(n)):
				if twist == 0:
					cj = sum([phi[0](gampow * teich[a] / p^(n+1)) for a in range(1,(p+1)/2)])
				else:
					cj = sum([teich[a]^twist * phi[0](gampow * teich[a] / p^(n+1)) for a in range(1,(p+1)/2)])					
				mt = mt + R(cj) * oneplusTpow
				gampow = gampow * gam
				oneplusTpow = oneplusTpow * (1 + T)
			end = time.time()
			t = end-start
			if t>=bigcall:
				line = E.label()+": p="+str(p)+", n="+str(n)
				line += ", time: "+str(end-start)+"\n"
				write_to_file(bigcallfile,line)

			ans = 2 * R(mt) * R(phi[1])
				##extra factor of 2 here is because we are only summing up to (p-1)/2
				##and using the + modular symbol
		else:
			assert n >= 0, "n must be non-negative when p=2"
			ap = E.ap(2)
			if n == 0:
				return R((ap^2 - 2*ap - 1) * phi[0](0) * phi[1])
			else:
				gam = 5
				Qp = pAdicField(p,2*n + 5)   ##Should check carefully the accuracy needed here
				gampow = 1
				oneplusTpow = 1
				for j in range(p^(n)):
					cj = phi[0](gampow/p^(n+2)) 
					mt = mt + cj*oneplusTpow
					gampow = gampow * gam
					oneplusTpow = oneplusTpow * (1 + T)
				end = time.time()
				t = end-start
				if t >= bigcall:
					line = E.label()+": p="+str(p)+", n="+str(n)
					line += ", time: "+str(end-start)+"\n"
					write_to_file(bigcallfile,line)
				ans = 2 * R(mt) * phi[1]
					## extra factor of 2 here arises because we are only summing over half of the
					## terms in the sum (only compute one of [a/2^n] and [(2^n-a)/2^n])
	end = time.time()
	if logfile != None:
		line = "   -Finished in "+str(round(end-start,2))+'\n'
		write_to_file(logfile,line)
	return ans




def mu_minimized_modular_symbol(C,sign=1,logfile=None):
	"""Searches through the isogeny class C and returns the modular symbol attached
		to the curve with the largest real (resp. imaginary depending on sign) period times number of 
		real components along with a list of scalars that takes the modular symbol of each curve in the 
		isogeny class to the modular symbol of E.

		Actually, this code doesn't return a modular symbol, but an ordered pair (phi,c) where phi is 
		the modular symbol and c is a constant to allow for rescaling of the modular symbol.  In this case.
		by 1/(# of real components) --- this will be removed once SAGE's modular symbols is updated.

	Inputs:

	-	``C`` -- isogeny class of elliptic curves given in the format from the function 
		CremonaDatabase().isogeny_classes()
	-	``sign`` -- 1 (default) or -1
	-	``logfile`` -- None (default) or string; if given then information about the computation is outputted
		to the file ``logfile``
	"""
	curves = [EllipticCurve(E[0]) for E in C]
	if sign == 1:
		periods = [E.period_lattice().basis()[0] * E.real_components() for E in curves]
	else:
		periods = [imag_part(E.period_lattice().basis()[1]) * E.real_components() for E in curves]
	max_period = max(periods)
	Emin = curves[periods.index(max_period)]
	if logfile != None:
		line = " Fetching modular symbol for "+Emin.label()+'\n'
		write_to_file(logfile,line)
		start = time.time()
	if sign == 1:
		phi = Emin.modular_symbol()
	else:
		phi = Emin.modular_symbol(sign=-1,implementation='sage')
	if logfile != None:
		end=time.time()
		line=" -Finished in "+str(round(end-start,2))+'\n'
		write_to_file(logfile,line)
	scale = []
	eps = 10^(-8)  ## some small number
	for a in range(len(periods)):
		assert abs(max_period/periods[a] - round(max_period/periods[a])) < eps, "Problem with period lattices"
		scale += [ZZ(round(max_period/periods[a]))]

	return (phi,1/Emin.real_components()),scale

def iwasawa_invariants_of_ec(E,p,twist=0,phi=None,scale=None,logfile=None,warnfile=None,bigcallfile=None,bigcall=infinity):
	"""
	Returns the mu and lambda invariants of E (for the prime p).  

	If twist is non-zero then it returns the twisted invariants (e.g. corresponding to E[p^infty] \otimes omega^twist)
	If the minimal mu-invariant fails to be 0, then '?' is returned for mu

	Input:

	-	``E`` -- elliptic curve

	-	``p`` -- prime

	-	``twist`` -- 0 (default) or integer between 0 and p-2 (explained above)

	-	``phi`` -- None (default) or an order pair where phi[0] is the modular symbol attached
		to an elliptic curve in the isogeny class of E (typically chosen to minimize the mu-invariant
		in the isogeny class) and phi[1] is a constant used to rescale phi[0] (typically chosen to be
		1/(# of real components of E).  This ordered pair business can be dropped once SAGE's 
		normalization problems with modular symbols is fixed

	-	``scale`` -- None (default) or integer; this constant is required is phi is specified in which
		case the constant represents the scalar needed to go from the given modular symbol phi to the
		modular symbol of E.

	-	``logfile`` -- None (default) or string; if given then information about the computation is outputted
		to the file ``logfile``

	-	``warnfile`` -- None (default) or string; if given then warnings about postive mu's are outputted
		to the file ``warnfile``

	- 	``bigcallfile`` -- string (see below)

	-	``bigcall`` -- infinity (Default) or some real number.  When specified, writes info to bigcallfile
		if the call to this function makes longer than ``bigcall``

	Output:

	In the ordinary case: lambda,mu
	In the supersingular case: (lambda^+,lambda^-),(mu^+,mu^-) 
	If the minimal mu wasn't found to be, then mu's are returned as '?'
	"""
	if twist%2 == 0:
		sign = 1
	else:
		sign = -1

	if phi != None:
		assert scale!=None,"Need to specify scale if phi is given"

	if phi == None:
		C = E.isogeny_class()
		v = [[E.a_invariants()] for E in C]
		phi,scale = mu_minimized_modular_symbol(v,sign=sign,logfile=logfile)
		scale = scale[0] 	## scale is a list of scalars for all curves in the isogeny class
				   		   	## E should be the 0th curve in the class, so we just take this number

	if E.is_ordinary(p):
		if (E.ap(p)%p != 1) and (phi[0](0)*phi[1]).valuation(p) == 0:
			return scale.valuation(p),0
		## If the conditions in this if statements hold, then L(E,1)/Omega_E is a p-adic unit and
		## p is non-anamolous.  This forces the constant term of the p-adic L-function to be a unit
		## and thus for mu and lambda to vanish (for the curve with minimal mu).  We thus return
		## lambda=0 and mu appropriately scaled.
		rho = E.galois_representation()
		globally_irred = rho.reducible_primes().count(p)==0
		if globally_irred:
			if E.ap(p)%p != 1 and p != 2:
				n = -1
			else:
				n = 1
			### In the non-anomalous p odd case, if theta_{-1} is a unit then mu=lambda=0
			### Otherwise, theta_-1 and theta_0 always have positive mu.
			done = false
			mt = 0
			while (not done) and (n <= mu_bail(p)):
				mt = MazurTate(E,p,n,phi=phi,twist=twist,modp=true,logfile=logfile,bigcallfile=bigcallfile,bigcall=bigcall)
				if ((mu(mt,p) == 0) and (lamb(mt,p) < p^n-p^(n-1))) or (n >= mu_bail(p)):
					done = true
				else:
					n = n + 1
			## In the globally irreducible case, lamb(mt,p) is bounded as n increases 
			## so the second inequality is eventually sastisfied.
			## Once that inequality is satisfied and mu-vanishes, then the Iwasawa invariants
			## of the Mazur-Tate element are the Iwasawa invariants of the p-adic L-function.
			## (see proof of Prop 3.7 of Pollack-Weston Duke paper)
			if mu(mt,p) != 0:
				line = 'For '+E.label()+' and p='+str(p)+' minimal mu is '+str(mu(mt,p))
				warnings.warn(line)
				if warnfile != None:
					write_to_file(warnfile,line+'\n')
				if logfile != None:
					write_to_file(logfile,'***'+line+'\n')
				return '?',lamb(mt,p)
			else:
				return mu(mt,p) + scale.valuation(p),lamb(mt,p)
#			assert mu(mt,p)==0, "minimal mu-invariant didn't vanish"
		else:
			## This is the globally reducible case
			## In this case, the lambda invariants of the Mazur-Tate elements could be unbounded.
			## Instead we p-stabilize and compute until mu=0.
			acc = 10
			S.<y> = PolynomialRing(pAdicField(p,acc))
			rs = (y^2 - E.ap(p)*y + p).roots()
			if rs[0][0].valuation() == 0:
				alpha = rs[0][0]
			else:
				alpha = rs[1][0]
			MTs = [MazurTate(E,p,0,phi=phi,twist=twist,logfile=logfile,bigcallfile=bigcallfile,bigcall=bigcall)]
			done = false
			n = 1
			while (not done) and (n <= mu_bail(p)):
				MTs += [MazurTate(E,p,n,phi=phi,twist=twist,logfile=logfile,bigcallfile=bigcallfile,bigcall=bigcall)]
				mt = MTs[n] - 1/alpha*MTs[n-1] * xi(p,n)  ## This is the Mazur-Tate element attached to f_alpha
				if (mu(mt,p) == 0) or (n >= mu_bail(p)):
					done = true
				else:
					n = n + 1
		if mu(mt,p) != 0:
			line = 'For '+E.label()+' and p='+str(p)+' minimal mu is '+str(mu(mt,p))
			warnings.warn(line)
			if warnfile != None:
				write_to_file(warnfile,line)
			if logfile != None:
				write_to_file(logfile,line)
			return '?',lamb(mt,p)
		else:
			return mu(mt,p) + scale.valuation(p),lamb(mt,p)
	elif E.is_supersingular(p):
		assert scale.valuation(p) == 0, 'Something wrong with isogeny in the supersingular case'
		if (phi[0](0) * phi[1]).valuation(p) == 0 and p != 2:
			return (scale.valuation(p),scale.valuation(p)),(0,0)
			### In this case theta_0 is a unit which forces theta_1 to be a unit
			### The three-term relation then forces that mu(theta_n)=0 and lambda(theta_n)=q_n
			### so that mu^\pm = lambda^\pm = 0.
		else:
			MTs = [MazurTate(E,p,1,phi=phi,twist=twist,modp=true,logfile=logfile,bigcallfile=bigcallfile,bigcall=bigcall),MazurTate(E,p,2,phi=phi,twist=twist,modp=true,logfile=logfile,bigcallfile=bigcallfile,bigcall=bigcall)]
			done = (mu(MTs[0],p) == 0) and (mu(MTs[1],p) == 0)
			n = 3
			while not done and (n <= mu_bail(p)):
				MTs += [MazurTate(E,p,n,phi=phi,twist=twist,modp=true,logfile=logfile,bigcallfile=bigcallfile,bigcall=bigcall)]
				done = (mu(MTs[n-1],p) == 0) and (mu(MTs[n-2],p) == 0)
				n = n + 1
			n = n - 1
#			assert mu(MTs[n-1],p)==0 and mu(MTs[n-2],p)==0, "minimal mu-invariant didn't vanish"
			if (n+p.valuation(2))%2 == 0:
				mu_plus = mu(MTs[n-2],p)
				lambda_plus = lamb(MTs[n-2],p)-qn(p,n-1)
				mu_minus = mu(MTs[n-1],p)
				lambda_minus = lamb(MTs[n-1],p)-qn(p,n)
			else:
				mu_minus = mu(MTs[n-2],p)
				lambda_minus = lamb(MTs[n-2],p)-qn(p,n-1)
				mu_plus = mu(MTs[n-1],p)
				lambda_plus = lamb(MTs[n-1],p)-qn(p,n)
			if mu_plus != 0:
				line='For '+E.label()+' and p='+str(p)+' mu+ is '+str(mu_plus)
				warnings.warn(line)
				if warnfile != None:
					write_to_file(warnfile,line+'\n')
				if logfile != None:
					write_to_file(logfile,line+'\n')
				mu_plus = '?'
			if mu_minus != 0:
				line='For '+E.label()+' and p='+str(p)+' mu- is '+str(mu_minus)
				warnings.warn(line)
				if warnfile != None:
					write_to_file(warnfile,line+'\n')
				if logfile != None:
					write_to_file(logfile,line+'\n')
				mu_minus = '?'
			if mu_plus == '?' or mu_minus == '?':
				return '?',(lambda_plus,lambda_minus)
			else:
				return (mu_plus,mu_minus),(lambda_plus,lambda_minus)

def data_p(C,p,phi=None,twist=0,scale=None,logfile=None,warnfile=None,bigcallfile=None,bigcall=infinity):
	"""
	Returns a list with each entry corresponding to a curve in the isogeny class.
	For such a fixed curve, we return either 'a' for additive, (lambda,mu) for ordinary primes
	and (lambda^+,lambda^-,0) for supersingular ones

	Input:

	-	``C`` -- isogeny class of elliptic curves given in the format from the function 
		CremonaDatabase().isogeny_classes()

	-	``p`` -- prime

	-	``phi`` -- None (default) or an order pair where phi[0] is the modular symbol attached
		to an elliptic curve in the isogeny class of E (typically chosen to minimize the mu-invariant
		in the isogeny class) and phi[1] is a constant used to rescale phi[0] (typically chosen to be
		1/(# of real components of E).  This ordered pair business can be dropped once SAGE's 
		normalization problems with modular symbols is fixed

	-	``twist`` -- 0 (default) or integer between 0 and p-2 (explained above)

	-	``scale`` -- None (default) or integer; this constant is required is phi is specified in which
		case the constant represents the scalar needed to go from the given modular symbol phi to the
		modular symbol of E.

	-	``logfile`` -- None (default) or string; if given then information about the computation is outputted
		to the file ``logfile``

	-	``warnfile`` -- None (default) or string; if given then warnings about postive mu's are outputted
		to the file ``warnfile``

	- 	``bigcallfile`` -- string (see below)

	-	``bigcall`` -- infinity (Default) or some real number.  When specified, writes info to bigcallfile
		if the call to this function makes longer than ``bigcall``

	Output:

	A list with each entry corresponding to the given curves in the isogeny class.
	Each entry is either:

	'a' -- for additive reduction
	'o?' -- unknown in ordinary or multiplicative case
	's?' -- unknown in supersingular case
	(lambda, mu) -- ordinary case
	(lambda^+, lambda^-, 0) -- supersingular case (if mu^+>0 or mu^- positive functions breaks)
	"""
	E = EllipticCurve(C[0][0])
	if phi == None:
		phi,scale = mu_minimized_modular_symbol(EllipticCurve(E),sign=(-1)^twist,logfile=logfile)

	if logfile != None:
		line = " Computing with p = "+str(p)+'\n'
		write_to_file(logfile,line)

	N=E.conductor()
	if E.has_additive_reduction(p):
		return ['a' for j in range(len(C))]

	## These lines deal with the fact that there are problems with 2-normalizations
	## in square-level

	if N.is_square() and (p==2):
		if E.is_ordinary(2):
			return ['?o' for j in range(len(C))]
		else:
			return ['?s' for j in range(len(C))]

	if E.is_ordinary(p):
		ans = []		
		m,l = iwasawa_invariants_of_ec(E,p,phi=phi,twist=twist,scale=1,logfile=logfile,warnfile=warnfile,bigcallfile=bigcallfile,bigcall=bigcall)
		for j in range(len(C)):
			if m != '?':
				ans = ans + [(l,m + scale[j].valuation(p))]
			else:
				ans = ans + ['o?']
	elif E.is_supersingular(p):
		ans = []
		ms,ls = iwasawa_invariants_of_ec(E,p,phi=phi,twist=twist,scale=1,logfile=logfile,warnfile=warnfile,bigcallfile=bigcallfile,bigcall=bigcall)
		for j in range(len(C)):
			assert scale[j].valuation(p) == 0, "p-isogeny for supersingular p???"
			if ms[0] != '?' and ms[1] != '?':
				ans = ans + [(ls[0],ls[1],0)]
			else:
				ans = ans + ['s?']
	return ans


def text_for_iwasawa_invariants_of_ec_isogeny_class(C,minp,maxp,twist=0,datafile=None,logfile=None,warnfile=None,bigcallfile=None,bigcall=infinity):
	"""
	Writes to file or screen strings containing the data of the iwasawa invariants for the curves 
	in a given isogeny class.

	Input:

	-	``C`` -- isogeny class of elliptic curves given in the format from the function 
		CremonaDatabase().isogeny_classes()

	-	``minp`` -- integer

	-	``maxp`` -- integer

	-	``twist`` -- 0 (default) or integer between 0 and p-2 (explained above)

	-	``datafile`` -- None (default) or string; if given then data is outputted to the file ``datafile``

	-	``logfile`` -- None (default) or string; if given then information about the computation is outputted
		to the file ``logfile``

	-	``warnfile`` -- None (default) or string; if given then warnings about postive mu's are outputted
		to the file ``warnfile``

	- 	``bigcallfile`` -- string (see below)

	-	``bigcall`` -- infinity (Default) or some real number.  When specified, writes info to bigcallfile
		if the call to this function makes longer than ``bigcall``

	Output:

	Data on each curve in the isogeny class is printed to screen or to the file datafile.

	For example:

	11 a 1 0,-1,1,-10,-20 7 1,0 0,1,0 0,0 0,1 

	The first 3 fields correspond to '11a1'.
	The next field are the a-invariants
	The next field is a constant q_0.  If q_0 is non-zero, then mu and lambda vanishes for all p>=q_0.
	The next fields are Iwasawa invariants for the primes of reduction.
	The following fields are Iwasawa invariants for the primes between minp and maxp.

	The following are the possible fields of Iwasawa invariants for a given prime
		'a' -- additive
		'o?' -- unknown ordinary case
		's?' -- unknown supersingular case
		lambda, mu -- ordinary invariants
		lambda^+,lambda^-,0 -- supersingular invariatns (if mu^\pm nonzero program crashes)
	"""
	start=time.time()
	E = EllipticCurve(C[0][0])
	N = E.conductor()
	if logfile != None:
		line = '\n' + "Working on isogeny class containing " + E.label() + '\n'
		write_to_file(logfile,line)
	phi,scale = mu_minimized_modular_symbol(C,sign=(-1)^twist,logfile=logfile)

	data_bad = []
	ps = N.factor()
	ps = [ps[a][0] for a in range(len(ps))]
	for p in ps:
		data_bad = data_bad + [data_p(C,p,phi=phi,twist=twist,scale=scale,logfile=logfile,warnfile=warnfile,bigcallfile=bigcallfile,bigcall=bigcall)]

	if phi[0](0)!=0 and E.torsion_order() > 1:
		rho = E.galois_representation()	
		if len(rho.reducible_primes()) > 0:
			max_red = max(rho.reducible_primes())
		else:
			max_red = 1
		L = phi[0](0).factor()
		if len(L) > 0:
			maxp = max(L[len(L)-1][0],max_red)
		else:
			maxp = max(2,max_red)  ##MAYBE THIS SHOULD BE ONE.  NEED TO CHECK a_2=-1
		if E.torsion_order().is_prime():
			maxp = max(maxp,E.torsion_order())
		q = next_prime(maxp)
	else:
		q = 0

	data = []
	for p in primes(minp,maxp+1):
		if N%p != 0:
			data = data + [data_p(C,p,phi=phi,twist=twist,scale=scale,logfile=logfile,warnfile=warnfile,bigcallfile=bigcallfile,bigcall=bigcall)]
		else:
			data = data + [data_bad[ps.index(p)]]

	for a in range(len(C)):
		E = EllipticCurve(C[a][0])
		lab = parse_cremona_label(E.label())
		line = str(lab[0]) + ' ' + str(lab[1]) + ' ' + str(lab[2]) + ' '
		line += str(E.a1()) + ','
		line += str(E.a2()) + ','
		line += str(E.a3()) + ','
		line += str(E.a4()) + ','
		line += str(E.a6()) + ' '
		line += str(q) + ' '
		for j in range(len(data_bad)):
			if isinstance(data_bad[j][a],type('?')):  ###that is, if it is a string
				line += data_bad[j][a] + ' '
			elif len(data_bad[j][a]) == 2:
				line += str(data_bad[j][a][0]) + ','
				line += str(data_bad[j][a][1]) + ' '
			else:
				line += str(data_bad[j][a][0]) + ','
				line += str(data_bad[j][a][1]) + ','
				line += str(data_bad[j][a][2]) + ' '			
		for j in range(len(data)):
			if isinstance(data[j][a],type('?')):  ###that is, if it is a string
				line += data[j][a] + ' '
			elif len(data[j][a]) == 2:
				line += str(data[j][a][0]) + ','
				line += str(data[j][a][1]) + ' '			
			else:
				line += str(data[j][a][0]) + ','
				line += str(data[j][a][1]) + ','
				line += str(data[j][a][2]) + ' '			
		line += '\n'
		print line,
		if datafile != None:
			write_to_file(datafile,line)
	if logfile != None:
		line = "----------------Total time: " + str(round(time.time()-start,2)) + '\n'
		write_to_file(logfile,line)
	del phi
	return "Done"


def collect_iwasawa_invariants_of_ecs(minC,maxC,minp,maxp,twist=0,datafile=None,logfile=None,warnfile=None,bigcallfile=None,bigcall=infinity):
	"""
	Top level function which rungs through all isogeny classes with conductors between minC and maxC
	and computes Iwasawa invariants for primes between minp and maxp.

	Input:

	-	``minC`` -- integer

	-	``maxC`` -- integer

	-	``minp`` -- integer

	-	``maxp`` -- integer

	-	``twist`` -- 0 (default) or integer between 0 and p-2 

	-	``datafile`` -- None (default) or string; if given then data is outputted to the file ``datafile``

	-	``logfile`` -- None (default) or string; if given then information about the computation is outputted
		to the file ``logfile``

	-	``warnfile`` -- None (default) or string; if given then warnings about postive mu's are outputted
		to the file ``warnfile``

	- 	``bigcallfile`` -- string (see below)

	-	``bigcall`` -- infinity (Default) or some real number.  When specified, writes info to bigcallfile
		if the call to this function makes longer than ``bigcall``
	"""

	DB = CremonaDatabase()
	for N in range(minC,maxC+1):
		if not ZZ(N).is_square():
			Cs = DB.isogeny_classes(N)
			for C in Cs:
				text_for_iwasawa_invariants_of_ec_isogeny_class(C,minp,maxp,twist=0,datafile=datafile,logfile=logfile,warnfile=warnfile,bigcallfile=bigcallfile,bigcall=bigcall)
	return "Done"

def mu(f,p):
	"""Returns the (p-adic) mu-invariant of f"""
	if f == 0:
		return oo
	else:
		return min([f[a].valuation(p) for a in range(f.degree()+1)])

def lamb(f,p):
	"""Returns the (p-adic) lambda-invariant of f"""
	if f == 0:
		return oo
	else:
		m = mu(f,p)
		v = [f[a].valuation(p) for a in range(f.degree()+1)]
		return v.index(m)


def xi(p,n):
	"""Returns the p^n-th cyclotomic polynomial evaluated at (1+T)"""
	R.<T> = PolynomialRing(QQ)
	if n == 0:
		return T
	else:
		ans = 0
		for j in range(p):
			ans = ans + (1 + T)^(j * p^(n-1))
		return ans

def qn(p,n):
	"""q_n as defined by Kurihara"""
	if n%2 == 0:
		return sum([p^a - p^(a-1) for a in range(1,n,2)])
	else:
		return sum([p^a - p^(a-1) for a in range(2,n,2)])


def collect_iwasawa_invariants_of_ecs_square_level(minC,maxC,minp,maxp,twist=0,datafile=None,logfile=None,warnfile=None,bigcallfile=None,bigcall=infinity):
	"""
	Top level function which rungs through all isogeny classes with square conductors between minC and maxC
	and computes Iwasawa invariants for primes between minp and maxp.

	Input:

	-	``minC`` -- integer

	-	``maxC`` -- integer

	-	``minp`` -- integer

	-	``maxp`` -- integer

	-	``twist`` -- 0 (default) or integer between 0 and p-2 

	-	``datafile`` -- None (default) or string; if given then data is outputted to the file ``datafile``

	-	``logfile`` -- None (default) or string; if given then information about the computation is outputted
		to the file ``logfile``

	-	``warnfile`` -- None (default) or string; if given then warnings about postive mu's are outputted
		to the file ``warnfile``

	- 	``bigcallfile`` -- string (see below)

	-	``bigcall`` -- infinity (Default) or some real number.  When specified, writes info to bigcallfile
		if the call to this function makes longer than ``bigcall``
	"""

	DB = CremonaDatabase()
	for N in range(minC,maxC+1):
		if ZZ(N).is_square():
			Cs = DB.isogeny_classes(N)
			for C in Cs:
				text_for_iwasawa_invariants_of_ec_isogeny_class(C,minp,maxp,twist=0,datafile=datafile,logfile=logfile,warnfile=warnfile,bigcallfile=bigcallfile,bigcall=bigcall)
	return "Done"

