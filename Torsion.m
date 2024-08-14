MyFrobCommand := "export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/sage/sage-9.5/local/lib/; /home/bommel/cap/controlledreduction-torsion/build/examples/myfrob";

// ANALYTIC RECONSTRUCTION

function FromMumfordRepresentation(J, MumRep : MaxDegree := 12, Debug := false)
	while MumRep[1] eq [] do
		Remove(~MumRep, 1);
	end while;
	CC := Parent(MumRep[1][1][2]);
	eps := 10^-Floor(Precision(CC)/2);
	K := Rationals();
	phi := hom< K->CC | >;
	R<x, y, z> := PolynomialRing(K, 3);
	RC<xC, yC, zC> := PolynomialRing(CC, 3);
	phiR := hom< R->RC | phi, [xC, yC, zC] >;
	Pols := [];
	// Find algebraic x-polynomial
	for i0 in [1..#MumRep] do
		Mf := MumRep[i0];
		Append(~Pols, R!0);
		for i in [1..#Mf] do
			C := Mf[i];
			FactorFound := false;
			for f in Factorisation(ChangeRing(C[1], K)) do
				fC := phiR(Evaluate(f[1], R.1));
				if Abs(Evaluate(fC, [C[2], 0, 0])) lt eps^(1/4) then
					if Degree(f[1])*AbsoluteDegree(K) gt MaxDegree then
						print "Field extension becoming too big";
						continue f;
					end if;
					FactorFound := true;
					if Degree(f[1]) eq 1 then
						L := K;
						rho := IdentityFieldMorphism(K);
						rhoR := hom< R->R | rho, [R.i : i in [1..Rank(R)]] >;
						a := Roots(f[1])[1][1];
					else
						L := Polredabs(AbsoluteField(ext< K | f[1] >) : Best := true);
						R1L := PolynomialRing(L);
						if K eq Rationals() then
							b := 1;
							rho := hom< K->L |>;
							rhof1 := hom< Parent(f[1])->R1L | rho, R1L.1 >;
						else
							for rt in Roots(DefiningPolynomial(K), L) do
								rho := hom< K->L | rt[1] >;
								rhof1 := hom< Parent(f[1])->R1L | rho, R1L.1 >;
								if #Roots(rhof1(f[1])) gt 0 then
									b := rt[1];
									break rt;
								end if;
							end for;
						end if;
						Rnew := ChangeRing(R, L);
						rhoR := hom< R->Rnew | rho, [Rnew.i : i in [1..Rank(Rnew)]] >;
						R := Rnew;
						a := Roots(rhof1(f[1]))[1][1];
						FoundComplexMap := false;
						for x in Roots(DefiningPolynomial(L), CC) do
							newphi := hom< L->CC | x[1] >;
							newphiR := hom< R->RC | newphi, [RC.i : i in [1..Rank(RC)]] >;
							if Abs(newphi(b) - phi(K.1)) lt eps^(1/4) then
								if Abs(newphi(a) - C[2]) lt eps^(1/4) then
									FoundComplexMap := true;
									break x;
								end if;							
							end if;
						end for;
						if not(FoundComplexMap) then
							return Zero(J);
						end if;
						phi := newphi;
						phiR := newphiR;
					end if;
					Pols := [rhoR(Pol) : Pol in Pols];
					Pols[i0] +:= a * &*[(R.k)^(C[3][k]) : k in [1..#C[3]]];
					K := L;
					break f;			
				end if;
			end for; // f
			if not(FactorFound) then
				return Zero(J);
			end if;
		end for; // i
	end for; // i0

	// Check polynomials
	for i0 in [1..#MumRep] do
		Mf := MumRep[i0];
		PolxR := phiR(Pols[i0]);
		assert(#Monomials(PolxR) le #Mf);
		ZeroIndices := {1..#Mf};
		for i in [1..#Monomials(PolxR)] do
			k := [j : j in [1..#Mf] | Mf[j][3] eq Exponents(Monomials(PolxR)[i])][1];
			assert( Abs( Coefficients(PolxR)[i] - Mf[k][2]) lt eps^(1/4) );
			Exclude(~ZeroIndices, k);
		end for;
		for i in ZeroIndices do
			assert( Abs(Mf[i][2]) lt eps^(1/10) );
		end for;
	end for;
	
	// Construct point on J
	JK := BaseChange(J, hom<Rationals()->K |>);
	CK := JK`C;
	RK<x, y, z> := CoordinateRing(Ambient(CK));
	I := ideal< RK | [Evaluate(p, [x,y,z]) : p in Pols] >;
	D := Divisor(CK, Saturation(I));
	Pt := Point(JK, D);
	assert(Debug eq false);
	return Pt;
end function;

function AnalyticPoint(P, CC)
	K := Parent(P[1]);
	AnP := [];
	for z in Roots(DefiningPolynomial(K), CC) do
		if K eq Rationals() then
			phi := hom<K -> CC | >;
		else
			phi := hom<K -> CC | z[1]>;
		end if;
		Append(~AnP, [phi(x) : x in P]);
	end for;
	return AnP;
end function;

function AnalyticDivision(C, J, Pt, l, lTorsion : PotMumfordReps := [], Precision := 200)
	// Find chart where the canonical point lies.
	I := Ideal(J`D_can);
	R<x,y,z> := CoordinateRing(Ambient(C));
	if (z in I) then
		if (y in I) then
			phi := hom< R->R | [y,z,x]>;
			phi_inv := [3,1,2];
		else
			phi := hom< R->R | [z,x,y]>;
			phi_inv := [2,3,1];
		end if;
	else
		phi := hom< R->R | [x,y,z] >;
		phi_inv := [1,2,3];
	end if;
	C2 := Curve(Ambient(C), phi(Equation(C)));
	I2 := ideal<R | [phi(x) : x in Generators(I)]>;
	D2 := Divisor(C2, I2);
	assert(IsEffective(D2));
	assert(Degree(D2) eq 1);
	J2 := GenericJacobian(C2, D2);
	BaseI := ideal<R | [phi(x) : x in Generators(Ideal(Pt))] >;
	BasePt := Point(J2, Divisor(C2, BaseI));
	// Construct Riemann surface
	_<v,w> := PolynomialRing(Rationals(), 2);
	f := Evaluate(Equation(C2), [v,w,1]);
	RS := RiemannSurface(f : Precision := Precision);
	BasePt_RS := RS!Coordinates(RepresentativePoint(Decomposition(D2)[1][1]));
	B := [BasePt_RS : i in [1..3]];
	if Pt`D eq 0 then
		v := AbelJacobi(BasePt_RS, BasePt_RS);
	else
		v := &+[w[2]*&+[AbelJacobi(BasePt_RS, RS!q) : q in AnalyticPoint(Coordinates(RepresentativePoint(w[1]))[phi_inv], ComplexField(Precision))] : w in Decomposition(Pt`D)];
	end if;
	// Construct analytic version of the lTorsion
	AnalyticTorsion := [];
	for Qt in lTorsion do
		if Qt`D eq 0 then
			v2 := AbelJacobi(BasePt_RS, BasePt_RS);
		else
			v2 := &+[w[2]*&+[AbelJacobi(BasePt_RS, RS!q) : q in AnalyticPoint(Coordinates(RepresentativePoint(w[1]))[phi_inv], ComplexField(Precision))] : w in Decomposition(Qt`D)];
		end if;
		Append(~AnalyticTorsion, v2);
	end for;
	
	print("Found analytic element, now try to divide by using Newton-Raphson");
	// Search for points
	if #PotMumfordReps eq 0 then
		PotMumfordReps, MumfordSucceeded := AnalyticTorsionSearch(C2, RS, B, v, l, AnalyticTorsion);
	end if;
	PotPts := [FromMumfordRepresentation(J2, MumRep) : MumRep in PotMumfordReps];
	// Translate results back to original Jacobian
	PotPtsOrig := [];
	for x in PotPts do
		if x eq 0 then
			continue x;
		end if;
		K := BaseField(x`J`C);
		JK := BaseChange(J, hom<Rationals()->K |>);
		CK := JK`C;
		I := Ideal(x);
		R := CoordinateRing(Ambient(CK));
		rho := hom< R->R | [R.(phi_inv[s]) : s in [1..3]]>;
		IK := ideal< R | [rho(s) : s in Generators(I)] >;
		D := Divisor(CK, IK);
		assert(Degree(D) eq Degree(x`D));
		Append(~PotPtsOrig, Point(JK, D));
	end for;
	// Check result
	for x in PotPtsOrig do
		assert(PointOverSmallestField(J, l*x) eq Pt);
	end for;
	assert(#PotPtsOrig gt 0);
	return PotPtsOrig;
end function;


// ALGEBRAIC RECONSTRUCTION 

function ReductionsToIdeal(L)
	n := LCM([Integers()!x[1] : x in L]);
	RZn<x> := PolynomialRing(Integers(n), 1);
	phi := hom< Parent(L[1][1])->RZn | x >;
	IdealList := [ideal< RZn | phi(P) > : P in L];
	return &meet(IdealList);
end function;

function FindSmallElement(I, maxDegree)
	Groebner(I);
	RZ<x> := PolynomialRing(Integers());
	phi := hom<I^0->RZ | x >;
	Mat := Matrix(&cat[ [ Coefficients(x^(maxDegree+1) + x^j * q)[1..maxDegree+1] : j in [0..maxDegree-Degree(q)] ] : q in [phi(x) : x in Generators(I)] cat [RZ!#BaseRing(I)] ]);
 	MatSh := LLL(Mat : Proof := false, EarlyReduction := true, Fast := 1); // Weight... TimeLimit := 5.0?
 	v := MatSh[1];
	return RZ![v[i] : i in [1..maxDegree+1]];
end function;

function AlgebraicReconstruction(L : maxDegree := 30, Verbose := false)
	I := ReductionsToIdeal(L);
	n := LCM([Integers()!x[1] : x in L]);
	for d in [1..maxDegree] do
		Pol := FindSmallElement(I, d);
		if 1000.0*(RealField()!MaxNorm(Pol)*2.0 + 1.0)^(1.1*(d+1)) gt n then
			if Verbose then
				print d;
				print Pol;
				print "Continue based on MaxNorm criterion";
			end if;
			continue d;
		end if;
		for x in L do
			p := Integers()!x[1];
			Pol_modp := ChangeRing(Pol, GF(p));
			Orig_modp := ChangeRing(x[2], GF(p));
			if (Pol_modp eq 0) or (Pol_modp mod Orig_modp ne 0) then
				if Verbose then
					print d;
					print Pol;
					print "Continue based on Pol_mod criterion";
				end if;
				continue d;
			end if;
		end for;
		return Pol;
	end for;
	return 0;
end function;

// GROUP STRUCTURE IN JACOBIAN
function FrobeniusPolynomial(f, pList)
	s := GetSeed();
	if Type(pList) ne SeqEnum then	// For backwards compatibility
		return FrobeniusPolynomial(f, [pList])[1];
	end if;
	
	R := PolynomialRing(Integers());
	d := TotalDegree(f);
	_<x,y,z> := Parent(f);
	Coeffs_x := Coefficients(f + x^(d+1), 1)[1..d+1];
	Coeffs_xy := [Evaluate(Coefficients(Coeffs_x[i] + y^(d+2-i),2)[1..(d+2-i)],[0,0,1]) : i in [1..d+1]];
	Coeffs := &cat(Coeffs_xy);
	FrobPolyList := [];
	TimeInControlledReduction := 0;
	
	for p in pList do
		F := Open("inputfile" cat Sprint(s), "w");
		Write(F, IntegerToString(p));
		Write(F, "\n[");
		// coefficients
		for i in [1..#Coeffs] do
			Write(F, IntegerToString(Integers()!GF(p)!Coeffs[i]));
			if i ne #Coeffs then
				Write(F, " ");
			end if;
		end for;
		// end coefficients
		Write(F, "]\n");
		delete F;
		
// /home/sage/sage-8.8/local/lib/
// /home/bommel/sage-8.8-lib/
		TimeInControlledReduction -:= Cputime();
		System(MyFrobCommand cat " 1 inputfile" cat Sprint(s) cat " outputfile" cat Sprint(s) cat " > erroroutput" cat Sprint(s));
		TimeInControlledReduction +:= Cputime();
		EvalOutput := Read("outputfile" cat Sprint(s));
		Append(~FrobPolyList, R!StringToIntegerSequence(EvalOutput[2..#EvalOutput-2]));
		System("rm inputfile" cat Sprint(s) cat " outputfile" cat Sprint(s) cat " erroroutput" cat Sprint(s));
	end for;
	print TimeInControlledReduction, "seconds spent in controlled_reduction computing Frobenius polynomials";
	return FrobPolyList;
end function;

function lDivisors(Jq, l, Pt)
	return [g : g in pSylowSubgroup(Jq, l) | (l*g eq Pt) and not(g eq Pt)];
end function;


// HELPER FUNCTIONS
function MyNormalisation(Pt)
	P := [Pt[i] : i in [1..3]];
	d := LCM([Denominator(x) : x in P]);
	P := [d*x : x in P];
	d := GCD([Numerator(x) : x in P]);
	P := [x/d : x in P];
	return P;
end function;

function IsSimpler(a, b)
	A := MyNormalisation(a);
	B := MyNormalisation(b);
	hA := Max([Abs(x) : x in A]);
	hB := Max([Abs(x) : x in B]);
	qA := &+[x^2 : x in A];
	qB := &+[x^2 : x in B];
	if hA ne hB then
		return hA - hB;
	elif qA ne qB then
		return qA - qB;
	elif A[1] ne B[1] then
		return A[1] - B[1];
	elif A[2] ne B[2] then
		return A[2] - B[2];
	else
		return A[3] - B[3];
	end if;
end function;

function UniqueElement(S)
	assert(#S eq 1);
	return Random(S);
end function;

procedure AddToPriorityQueue(~PriorityQueue, ~Total, S, k)
	if not(k in Keys(PriorityQueue)) then
		PriorityQueue[k] := {};
	end if;
	if not(S in PriorityQueue[k]) then
		Include(~PriorityQueue[k], S);
		Total +:= Max(k,1);
	end if;
end procedure;

procedure RemoveFromPriorityQueue(~PriorityQueue, ~Total)
	s := Max(Keys(PriorityQueue));
	S := Random(PriorityQueue[s]);
	if #PriorityQueue[s] eq 1 then
		Remove(~PriorityQueue, s);
	else
		Exclude(~PriorityQueue[s], S);
	end if;
	Total -:= Max(s,1);
end procedure;

function nfisincl(f,g) // Thanks to Andrew Sutherland
    assert (BaseRing(f) eq Rationals() or BaseRing(f) eq Integers()); //: "The polynomial f must have coefficients in Q.";
    assert (BaseRing(g) eq Rationals() or BaseRing(g) eq Integers()); //: "The polynomial g must have coefficients in Q.";
    f := ChangeRing(f, Rationals());
    g := ChangeRing(g, Rationals());
    R<x> := Parent(g);
    f := Evaluate(f,x);
    cmd:=Sprintf("{print(nfisincl(%o,%o))}",f,g);
    s := Pipe("gp -q", cmd);
    s := eval(s);
    if Type(s) ne SeqEnum then return [Parent(g)|]; end if;
    return [Parent(g)|Evaluate(R!h,x):h in s];
end function;

function MyCompositeFields(K,L : MaxDegree := 12)
	if IsPrimeField(K) then
		if IsFinite(L) then
			Lopt := L;
			phiL := IdentityFieldMorphism(L);
		else
			Lopt, phiL := Polredabs(L : Best := true);
		end if;
		return [* < hom<K->Lopt|>, phiL > *];
	elif IsPrimeField(L) then
		if IsFinite(K) then
			Kopt := K;
			phiK := IdentityFieldMorphism(K);
		else
			Kopt, phiK := Polredabs(K : Best := true);
		end if;
		return [* < phiK, hom<L->Kopt|> > *];
	elif IsFinite(K) then
		M := K+L;
		phi1 := hom<K->M | K.1>;
		phi2 := hom<L->M | L.1>;
		return [* <phi1, phi2> *];
	end if;
	f := DefiningPolynomial(K);
	g := DefiningPolynomial(L);
	RelevantPairs := [* *];
	for M2 in CompositeFields(K,L) do
		if AbsoluteDegree(M2) gt MaxDegree then
			continue M2;
		end if;
		for x in RelevantPairs do
			if IsIsomorphic(x[1], M2) then
				continue M2;
			end if;
		end for;
		M := Polredabs(M2 : Best := true);
		AutM := Automorphisms(M);
		h := DefiningPolynomial(M);
		ImagesK := [ Evaluate(phi, M.1) : phi in nfisincl(f,h)];
		ImagesL := [ Evaluate(phi, M.1) : phi in nfisincl(g,h)];
		for a in ImagesK do
			for b in ImagesL do
				for N in Subfields(M) do
					if (AbsoluteDegree(N[1]) lt AbsoluteDegree(M)) and (a in N[1]) and (b in N[1]) then
						continue b; // N is not a composite field in this case
					end if;
				end for; // N
				for x in RelevantPairs do
					if x[1] ne M then
						continue x;
					end if;
					for sigma in AutM do
						if (sigma(x[2]) eq a) and (sigma(x[3]) eq b) then
							continue b;
						end if;
					end for; // sigma
				end for; // x
				Append(~RelevantPairs, < M, a, b >);
			end for; // b
		end for; // a
	end for; // M2
	return [* < hom<K->x[1] | x[2]>, hom<L->x[1] | x[3]> > : x in RelevantPairs *];
end function;


function MyPlus(J, P, Q : MaxFieldDegree := 12)
	K := BaseField(P`J`C);
	L := BaseField(Q`J`C);
	PointList := {};
	for phi in MyCompositeFields(K,L : MaxDegree := MaxFieldDegree) do
	
		if not(IsFinite(K)) and (AbsoluteDegree(Codomain(phi[1])) gt MaxFieldDegree) then
			continue phi;
		end if;
		
		if IsFinite(K) then
			M := Codomain(phi[1]);
			if not(#M in Keys(J`ReductionObj)) then
				b, p := IsPrimePower(#M);
				J`ReductionObj[#M] := BaseChange(Reduction(J,p), hom<GF(p)->M|>);
			end if;
			JM_K := J`ReductionObj[#M];
			JM_L := JM_K;
			M := BaseField(JM_K`C);
			if IsPrimeField(K) then
				phiK := FieldMorphism(hom<K->M|>);
			else
				try
					if K eq M then
						phiK := IdentityFieldMorphism(K);
					else
						phiK := FieldMorphism(hom<K->M|Roots(MinimalPolynomial(K.1), M)[1][1]>);
					end if;
				catch e
					phiK := FieldMorphism(hom<K->M|Roots(MinimalPolynomial(K.1), M)[1][1]>);
				end try;
			end if;
			if IsPrimeField(L) then
				phiL := FieldMorphism(hom<L->M|>);
			else
				try
					if L eq M then
						phiL := IdentityFieldMorphism(L);
					else
						phiL := FieldMorphism(hom<L->M|Roots(MinimalPolynomial(L.1), M)[1][1]>);
					end if;
				catch e
					phiL := FieldMorphism(hom<L->M|Roots(MinimalPolynomial(L.1), M)[1][1]>);
				end try;
			end if;
			RM := CoordinateRing(Ambient(JM_K`C));
			rhoK := hom<CoordinateRing(Ambient(P`J`C))->RM | phiK, [RM.i : i in [1..Rank(RM)]]>;
			rhoL := hom<CoordinateRing(Ambient(Q`J`C))->RM | phiL, [RM.i : i in [1..Rank(RM)]]>;			
		else
			phiK := FieldMorphism(phi[1]);
			if IsIdentity(phiK) then
				phiL := FieldMorphism(phi[2]);
			else
				phiL := FieldMorphism(phi[1]);
			end if;
			JM_K, rhoK := BaseChange(P`J, phi[1]);
			JM_L, psiL := BaseChange(Q`J, phi[2]);
			if IsIdentity(phi[1]) then
				rhoL := psiL;
			else
				rhoL := hom<Domain(psiL)->Codomain(rhoK) | phi[2], [ Codomain(rhoK)!psiL(Domain(psiL).i) : i in [1..Rank(Domain(psiL))]]>;
			end if;
		end if;
		
		if IsIdentity(phiK) then
			PM := P;
		else
			PM := BaseChange(P, JM_K, rhoK);
		end if;
		if IsIdentity(phiL) then
			QM := Q;
		else
			QM := BaseChange(Q, JM_K, rhoL);
		end if;
		Include(~PointList, PointOverSmallestField(J, PM+QM));
	end for;
	return PointList;
end function;

function MyConjugates(P)
	K := BaseField(P`J`C);
	A := Automorphisms(K);
	R := CoordinateRing(Ambient(P`J`C));
	rho := [hom<R->R | phi, [R.i : i in [1..Rank(R)]]> : phi in A];
	return [ BaseChange(P, P`J, r) : r in rho ];
end function;

function MyEq(P, Q)
	K := BaseField(P`J`C);
	L := BaseField(Q`J`C);
	M := CompositeFields(K, L)[1];
	for x in Roots(ChangeRing(DefiningPolynomial(K),M)) do
		for y in Roots(ChangeRing(DefiningPolynomial(L),M)) do
			if K eq Rationals() then
				phiK := hom<K->M |>;
			else
				phiK := hom<K->M | x[1]>;
			end if;
			if L eq Rationals() then
				phiL := hom<L->M |>;
			else
				phiL := hom<L->M | y[1]>;
			end if;
			JM_K, rhoK := BaseChange(P`J, phiK);
			JM_L, rhoL := BaseChange(Q`J, phiL);
			rhoL := hom<Domain(rhoL)->Codomain(rhoK) | [ Codomain(rhoK)!rhoL(Domain(rhoL).i) : i in [1..Rank(Domain(rhoL))]]>;
			PM := BaseChange(P, JM_K, rhoK);
			QM := BaseChange(Q, JM_K, rhoL);
			if PM eq QM then
				return true;
			end if;
		end for;
	end for;
	return false;
end function;

function MyIn(P, S)
	for s in S do
		if MyEq(P, s) then
			return true;
		end if;
	end for;
	return false;
end function;

procedure MyAddElementToSubgroup(~S, x)
	assert(false);
	n := 1;
	nx := x;
	T := {};
	while not(MyIn(nx, S)) do
		Include(~T, nx);
		nx +:= x;
	end while;
	Snew := S;
	for s in S do
		for t in T do
			Include(~S, MyPlus(s,t));
		end for;
	end for;
end procedure;

procedure AddElementToSubgroup(~S, x)
	n := 1;
	nx := x;
	T := {};
	while not(nx in S) do
		Include(~T, nx);
		nx +:= x;
	end while;
	Snew := S;
	for s in S do
		for t in T do
			Include(~S, s+t);
		end for;
	end for;
end procedure;

procedure AddElementToSubgroup2(~S, x, ~V)
	n := 1;
	nx := x;
	T := {};
	while not(nx in S) do
		Include(~T, nx);
		nx +:= x;
	end while;
	Snew := S;
	for s in S do
		for t in T do
			Include(~S, s+t);
			Include(~V, s+t);
		end for;
	end for;
end procedure;

function xPolynomial(E, RZ, p)
	xPoly := RZ!1;
	for D in Decomposition(E) do
		I := Ideal(D[1]);
		Idehom := ideal< I^0 | [Evaluate(g, [I.1, I.2, 1]) : g in Generators(I)] cat [I.3]>;
		if Idehom ne Idehom^0 then
			xPoly *:= Evaluate(UnivariateEliminationIdealGenerator(Idehom, 1), [RZ.1, 0, 0]);
			if p ne 0 then
				xPoly mod:= p;
			end if;
		end if;
	end for;
	return xPoly;
end function;

function yPolynomial(E, RZ, p)
	yPoly := RZ!1;
	for D in Decomposition(E) do
		I := Ideal(D[1]);
		Idehom := ideal< I^0 | [Evaluate(g, [I.1, I.2, 1]) : g in Generators(I)] cat [I.3]>;
		if Idehom ne Idehom^0 then
			yPoly *:= Evaluate(UnivariateEliminationIdealGenerator(Idehom, 2), [0, RZ.1, 0]);
			if p ne 0 then
				yPoly mod:= p;
			end if;
		end if;
	end for;
	return yPoly;
end function;

function PolynomialRadical(f)
	if Degree(f) le 0 then
		return f;
	end if;
	return &*[g[1] : g in Factorisation(f)];
end function;

function DefinesActualJacobianPoint(J, Lx, Ly : MaxDegree := 1, ExpectedNumberOfPoints := 1)
	K := BaseField(J`C);
	R<x> := PolynomialRing(K);
	Pts := [* *];
	print "Lx = ", Lx;
	print "Ly = ", Ly;
	
	// First construct all possible polynomials from Lx, Ly and K
	Possibilities := [* [* R!0, R!0, K *] *];
	for i in [1..#Lx] do
		NewPossibilities := [* *];
		for p in Possibilities do
			L := p[3];
			for f in Factorisation(ChangeRing(Lx[i], L)) do
				if IsFinite(L) then
					AbsDeg := Degree(L);
				else
					AbsDeg := AbsoluteDegree(L);
				end if;
				if Degree(f[1])*AbsDeg gt MaxDegree then
					continue f;
				elif Degree(f[1]) eq 1 then
					Lnew := L;
					a := Roots(f[1])[1][1];
				else
					Lnew<a> := AbsoluteField(ext< L | f[1] >);
				end if;
				Polxnew := p[1] + a*ChangeRing(x, Lnew)^(i-1);
				Lnew_opt, phi_L := Polredabs(Lnew : Best := true);
				RL_opt := ChangeRing(Parent(Polxnew), Lnew_opt);
				rho_L := hom< Parent(Polxnew)->RL_opt | phi_L, [RL_opt.i : i in [1..Rank(RL_opt)]] >;
				Append(~NewPossibilities, [* rho_L(Polxnew), p[2], Lnew_opt *]);
			end for;
		end for;
		Possibilities := NewPossibilities;
	end for;
	for i in [1..#Ly] do
		NewPossibilities := [* *];
		for p in Possibilities do
			L := p[3];
			for f in Factorisation(ChangeRing(Ly[i], L)) do
				if IsFinite(L) then
					AbsDeg := Degree(L);
				else
					AbsDeg := AbsoluteDegree(L);
				end if;
				if Degree(f[1])*AbsDeg gt MaxDegree then
					continue f;
				elif Degree(f[1]) eq 1 then
					Lnew := L;
					a := Roots(f[1])[1][1];
				else
					Lnew<a> := AbsoluteField(ext< L | f[1] >);
				end if;
				Polynew := p[2] + a*ChangeRing(x, Lnew)^(i-1);
				Lnew_opt, phi_L := Polredabs(Lnew : Best := true);
				RL_opt := ChangeRing(Parent(Polynew), Lnew_opt);
				rho_L := hom< Parent(Polynew)->RL_opt | phi_L, [RL_opt.i : i in [1..Rank(RL_opt)]] >;
				Append(~NewPossibilities, [* rho_L(ChangeRing(p[1], Lnew)), rho_L(Polynew), Lnew_opt *]);
			end for;
		end for;
		Possibilities := NewPossibilities;
	end for;
	print #Possibilities, "possibilities found";
	
	// Then construct all possible points on J
	for p in Possibilities do
		print "Try possibility", p;
		PotPts := {};
		assert(K eq PrimeField(K)); // NotImplementedError
		//print "Degree number field:", AbsoluteDegree(K);
		//L := SplittingField([f[1] : f in Factorisation(p[1])]);
		L := p[3];
		CL := BaseChange(J`C, L);
		_<xL, yL> := FunctionField(CL);
		
		MaxInfinityDegree := (ExpectedNumberOfPoints*Genus(CL) - Degree(p[1])) / ExpectedNumberOfPoints;

		//print "All rings constructed";
		Dx := Numerator(Divisor(CL, Evaluate(p[1], xL)));
		//print "Dx computed";
		Dy := Numerator(Divisor(CL, Evaluate(p[2], yL)));
		//print "Dy computed";
		D := GCD(Dx, Dy);
		if (D eq 0) and (L ne Rationals()) and (p[1] ne ConstantCoefficient(p[1])) and (p[2] ne ConstantCoefficient(p[2])) then
			continue p;
		end if;
		//print "D constructed";
		
		Dnum := Numerator(D);
		//Inum := Ideal(Dnum);
		Dnum_decomp := Decomposition(Dnum);
		//print "Dnum constructed";
		Dden := Denominator(Divisor(CL, xL)) + Denominator(Divisor(CL, yL));
		//Iden := Ideal(Dden);
		Dden_decomp := Decomposition(Dden);
		//print "Dden constructed";
		//print "Divisors found, Dnum has", #Decomposition(Dnum), "components and Dden has", #Decomposition(Dden), "components";
		if Dnum ne 0 then
			print Decomposition(Dnum);
		end if;
		L1 := L;
		for K0 in [* (ResidueClassField(E[1])) : E in Dnum_decomp cat Dden_decomp *] do
			print "K0 =", K0;
			K1 := AbsoluteField(K0);
			print "K1 =", K1;
			L1 := CompositeFields(L1, K1)[1];
			if L1 ne Rationals() then
				print "Gal =", GaloisGroup(L1);
			end if;
		end for;
		if L1 ne Rationals() then
			G := GaloisGroup(L1);
			Subgrps := [H`subgroup : H in Subgroups(G) | H`order ge Order(G)/MaxDegree];
			Subf := [* NumberField(GaloisSubgroup(L1, H)) : H in Subgrps *];
		else
			Subf := [* Rationals() *];
		end if;
		PolynomialsSeen := {};
		for F in Subf do
			M := Polredabs(F : Best := true);
			if DefiningPolynomial(M) in PolynomialsSeen then
				continue F;
			end if;
			Include(~PolynomialsSeen, DefiningPolynomial(M));
			if AbsoluteDegree(M) gt MaxDegree or (Type(M) eq FldRat and L ne Rationals()) or not(L subset M) then
				continue F;
			end if;
			for rt in [ Evaluate(phi, M.1) : phi in nfisincl(DefiningPolynomial(L),DefiningPolynomial(M))] do
				print "Trying field", M, "root", rt;
				JM, rhoM := BaseChange(J, hom< K->M | >);
				CM := JM`C;
				RL := CoordinateRing(Ambient(CL));
				RM := CoordinateRing(Ambient(CM));
				PM := PolynomialRing(M);
				if Type(L) eq FldRat then
					phi := hom<L->M | >;
					rho := hom<RL->RM | [RM.i : i in [1..Rank(RM)]]>;
					psi := hom<Parent(p[1])->PM | PM.1 >;
				else
					phi := hom<L->M | rt>;
					rho := hom<RL->RM | phi, [RM.i : i in [1..Rank(RM)]]>;
					psi := hom<Parent(p[1])->PM | phi, PM.1 >;
				end if;
				p1M := psi(p[1]);
				DnumM_decomp := [];
				for E in Dnum_decomp do
					IM := ideal< RM | [rho(x) : x in Generators(Ideal(E[1])) ]>;
					EM := Divisor(CM, IM);
					for F in Decomposition(EM) do
						Append(~DnumM_decomp, < F[1], E[2]*F[2], xPolynomial(Divisor(F[1]), PM, 0) >);
					end for;
				end for;
				//InumM := ideal< RM | [rho(x) : x in Generators(Inum)]>;
				//DnumM := Divisor(CM, InumM);
				print "DnumM constructed";
				for D in DnumM_decomp do
					print D[1], Degree(D[1]);
				end for;
				DdenM_decomp := [];
				for E in Dden_decomp do
					IM := ideal< RM | [rho(x) : x in Generators(Ideal(E[1])) ]>;
					EM := Divisor(CM, IM);
					for F in Decomposition(EM) do
						Append(~DdenM_decomp, < F[1], E[2]*F[2], xPolynomial(Divisor(F[1]), PM, 0) >);
					end for;
				end for;
				//IdenM := ideal< RM | [rho(x) : x in Generators(Iden)]>;
				//DdenM := Divisor(CM, IdenM);
				//print "Base change done";
				
				NumeratorDivisors := [ { <DivisorGroup(CM)!0, PM!1 > } ];
				for i in [1..Genus(CL)] do
					Append(~NumeratorDivisors, {});
					for D in DnumM_decomp do
						k := Degree(D[1]);
						if k le i then
							for E in NumeratorDivisors[i+1-k] do
								if IsDivisibleBy(p1M, PolynomialRadical(D[3]*E[2])) then
									Include(~NumeratorDivisors[i+1], < D[1]+E[1], D[3]*E[2] >);
								end if;
							end for;
						end if;
					end for;
				end for;
				print "p1M =", p1M;
				print "NumeratorDivisors finished", [#NumeratorDivisors[i] : i in [1..Genus(CL)+1]];
				
				DenominatorDivisors := [ {<DivisorGroup(CM)!0, PM!1 >} ];
				for i in [1..Genus(CL)] do
					Append(~DenominatorDivisors, {});
					if i gt MaxInfinityDegree then
						continue i;
					end if;
					for D in DdenM_decomp do
						k := Degree(D[1]);
						if k le i then
							for E in DenominatorDivisors[i+1-k] do
								if IsDivisibleBy(p1M, PolynomialRadical(D[3]*E[2])) then
									Include(~DenominatorDivisors[i+1], < D[1]+E[1], D[3]*E[2] >);
								end if;
							end for;
						end if;
					end for;
				end for;
				print "DenominatorDivisors finished", [#DenominatorDivisors[i] : i in [1..Genus(CL)+1]];
				
				for i in [0..Genus(CL)] do
					for D in NumeratorDivisors[i+1] do
						for j in [0..Genus(CL)-i] do
							for E in DenominatorDivisors[j+1] do
								xPol := D[2]*E[2];
								if IsDivisibleBy(p1M, PolynomialRadical(xPol)) then
									Pt_sm := PointOverSmallestField(J, Point(JM, D[1]+E[1]));
									if AbsoluteDegree(BaseField(Pt_sm`J`C)) ne AbsoluteDegree(M) then
										continue E;
									end if;
									R_sm := CoordinateRing(Ambient(Pt_sm`J`C));
									rho_sm := hom< CoordinateRing(Ambient(J`C))->R_sm | [R_sm.i : i in [1..Rank(R_sm)]] >;
									Append(~Pts, [* Pt_sm, Pt_sm`J, rho_sm *]);
								end if;
							end for; // end for E
						end for; // end for j
					end for; // end for D
				end for; // end for i
			end for; // end for rt
		end for; // end for F
	end for; // end for p
	
	return Pts;
end function;

// DIVISION BY ALGEBRAIC RECONSTRUCTION
function DivisionByRationalReconstruction(J, Pt, l, PrimeList : BaseDegree := 1, MaxNumberOfReconstructions := 2*10^3, MaxDegree := 4, JpList := [], MaxSubgroupSize := 5000, lTorsion := {}, ExtraPrimes := [])
	// Preparation: assertions
	assert IsPrime(l);
	n := l*Order(Pt);
	assert n gt 0;
	Include(~lTorsion, Zero(J));
	Pt_red := AssociativeArray();
	for p in PrimeList do
		Pt_red[p] := UniqueElement(PrimeReduction(J, Pt, p));
	end for;
	
	// Step 1: finding the relevant points
	RQ := PolynomialRing(Rationals());
	RZ := PolynomialRing(Integers());
	Lx := [];
	Ly := [];
	IndexList := [i : i in [1..#PrimeList] | l^Valuation(Order(JpList[i]), l) lt MaxSubgroupSize];
	for i in IndexList do
		p := PrimeList[i];
		if JpList ne [] then
			Jp := JpList[i];
		else
			Jp := BaseChange(J, GF(p^BaseDegree));
		end if;
		PotElems := lDivisors(Jp, l, Pt_red[p]);
		if #PotElems eq 0 then
			return {};
		end if;
		xList := [];
		yList := [];
		for i in [1..#PotElems] do
			x := PotElems[i];
			if InputRepresentations(x) ne [] then
				if n gt l then
					InputRepsList := [InputRepresentations(x+UniqueElement(PrimeReduction(J, t, p)))[1] : t in lTorsion];			
					ExpectedNumberOfPoints := #lTorsion;	
				else
					InputRepsList := [InputRepresentations(x)[1]];
					ExpectedNumberOfPoints := 1;
				end if;
				xPoly := &*[xPolynomial(D, RZ, p) : D in InputRepsList] mod p;
				xPoly +:= RZ.1^(&+[Degree(D) : D in InputRepsList]+1);
				if not([xPoly, Degree(xPoly)-1] in xList) then
					yPoly := &*[yPolynomial(D, RZ, p) : D in InputRepsList] mod p;
					yPoly +:= RZ.1^(&+[Degree(D) : D in InputRepsList]+1);
					Append(~xList, [xPoly, Degree(xPoly)-1]);
					Append(~yList, [yPoly, Degree(yPoly)-1]);
				end if;
			end if;
		end for;
		Append(~Lx, xList);
		Append(~Ly, yList);
	end for;
	
	print "Step 1 finished - Found list of points modulo primes";
	
	// Step 2: finding the subsets of PrimeList to consider
	CopyLx := Lx;
	while #IndexList gt 15 do
		m, i := Max([#Lx[i] : i in [1..#Lx]]);
		Remove(~Lx, i);
		Remove(~Ly, i);
		Remove(~IndexList, i);
	end while;
	assert(#Lx eq #IndexList);
	
	TotalToConsider := 0;
	sizeL := [#Lx[i] : i in [1..#Lx]];
	PriorityQueue := AssociativeArray();
	for i in [1..#Lx] do
		for S in Subsets({1..#Lx},i) do
			if S ne {} then
				AddToPriorityQueue(~PriorityQueue, ~TotalToConsider, S, &*[sizeL[i]: i in S] + #S/ MaxNumberOfReconstructions^2);
				if TotalToConsider gt 10*MaxNumberOfReconstructions then
					break i;
				end if;
				//print "Added", S, "to priority queue";
			end if;
		end for;
	end for;
	
	while TotalToConsider gt MaxNumberOfReconstructions do
		RemoveFromPriorityQueue(~PriorityQueue, ~TotalToConsider);
	end while;
	
	SubsetsToConsider := {};
	
	print "Step 2 finished - Found appropriate subsets of primes";
	
	RemovalList := [];
	PointsFound := {};
	LcxTried := {};
	LcxTriedSuccess := {};
	TotalNrOfPointsFound := 0;
	for s in Sort([x : x in Keys(PriorityQueue)]) do
		for S in PriorityQueue[s] do
			//print S;
			LxS := Lx[ [x : x in S] ];
			LyS := Ly[ [x : x in S] ];
			LpS := PrimeList[ [IndexList[x] : x in S] ];
			IndicesS := [ [1..#x] : x in LxS ];
			for i in CartesianProduct(IndicesS) do
			
				Degx := {LxS[j][i[j]][2] : j in [1..#S]};
				Degy := {LyS[j][i[j]][2] : j in [1..#S]};
				if (#Degx gt 1) or (#Degy gt 1) then
					continue i; // Only try the reconstruction step is the degree of the polynomials is the same for all points modulo primes.
				end if;
				Degx := Random(Degx);
				Degy := Random(Degy);
				
				// Constructing minimal polynomials for coefficients
				Lcx := [];
				for k in [1..Degx+1] do
					MinimalPolynomials := [* MinimalPolynomial(Coefficients(LxS[j][i[j]][1])[k]) : j in [1..#S] *];
					ReconstructionList := [ [ LpS[j], ChangeRing(MinimalPolynomials[j], Integers()) ] : j in [1..#S] ];
					CoeffPol := AlgebraicReconstruction(ReconstructionList : maxDegree := 2*MaxDegree);
					if not(IsIrreducible(CoeffPol)) then
						continue i;
					else
						print "Success:", S, i, CoeffPol;
					end if;
					Append(~Lcx, CoeffPol);
				end for;
				
				Lcy := [];
				for k in [1..Degy+1] do
					MinimalPolynomials := [* MinimalPolynomial(Coefficients(LyS[j][i[j]][1])[k]) : j in [1..#S] *];
					ReconstructionList := [ [ LpS[j], ChangeRing(MinimalPolynomials[j], Integers()) ] : j in [1..#S] ];
					CoeffPol := AlgebraicReconstruction(ReconstructionList : maxDegree := 2*MaxDegree);
					if not(IsIrreducible(CoeffPol)) then
						continue i;
					end if;
					Append(~Lcy, CoeffPol);
				end for;
				
				
				if Lcx in LcxTried then
					if Lcx in LcxTriedSuccess then
						for j in [1..#S] do
							Append(~RemovalList, [* LpS[j], LxS[j][i[j]] *]); // for prime LpS[j] remove current L-entry
						end for;
					end if;
					continue i;
				end if;
				print Lcx, Lcy;
				CurrentPointsFound := DefinesActualJacobianPoint(J, Lcx, Lcy : MaxDegree := MaxDegree, ExpectedNumberOfPoints := ExpectedNumberOfPoints);
				//print CurrentPointsFound;
				Include(~LcxTried, Lcx);
				print "Start checking", #CurrentPointsFound, "potential new points";
				for P in CurrentPointsFound do
					//print Decomposition(P[1]`D);
					if P[1] in PointsFound then
						continue P;
					end if;
				
					K := BaseField(P[2]`C);
					GenDenominator := LCM([Denominator(c) : c in Coefficients(DefiningPolynomial(K))]);
					OK := RingOfIntegers(K);
					for p in PrimeList do //cat ExtraPrimes do // TODO change
						try
							Pt_p := Pt_red[p];
							for P1_p in PrimeReduction(J, P[1], p : OnlyLinear := true) do
								lP1_p := l*P1_p; //PointOverSmallestField(J, l*P1_p);
								if lP1_p ne Pt_p then
									//print "Point not added - finite field";
									continue P;
								end if;
							end for;
						catch e
							print "Finite field computation failed";
							print e;
							continue p;
						end try;						
					end for;
					
					if PointOverSmallestField(J, l*P[1]) eq Pt then 
						//Include(~PointsFound, P[1]);
						//print "POINT ADDED";
						for Q in lTorsion do
							if IsPrimeField(K) then
								R := P[1] + Q;
							else
								R := P[1] + BaseChange(Q, P[2], P[3]);
							end if;
							//if PointOverSmallestField(J, l*R) eq Pt then
							Include(~PointsFound, R);
							//end if;
						end for;
						Include(~LcxTriedSuccess, Lcx);
						for j in [1..#S] do
							Append(~RemovalList, [* LpS[j], LxS[j][i[j]] *]); // for prime LpS[j] remove current L-entry
						end for;
					else
						print "Point not added - number field";
					end if;
				end for;				
			end for;
			//print "Finished checking potential new points";
			//assert(false);
			
			// Pruning
			for x in RemovalList do
				p := x[1];
				i := Index(IndexList, Index(PrimeList, p));
				OldOrder := #Lx[i];
				j := Index(Lx[i], x[2]);
				while (j ne 0) do
					Remove(~Lx[i], j);
					Remove(~Ly[i], j);
					j := Index(Lx[i], x[2]);
				end while;
				NewOrder := #Lx[i];
				//if OldOrder ne NewOrder then
				//	print "Successful removal";
				//end if;
				if #Lx[i] eq 0 then
					return PointsFound;
				end if;
			end for;
			
		end for;
	end for;
	
	return PointsFound;
end function;

procedure GuessOrder(J, WeilPolynomial_modq)
	// Inequalities by SAFIA HALOUI
	q := #BaseField(J`C);
	Coeffs := [c mod q : c in Coefficients(WeilPolynomial_modq)];
	assert (Coeffs[4] mod q) ne 0;
	sqrt_q := Sqrt(q);
	RZ := Parent(WeilPolynomial_modq);
	PotentialOrders := [];
	
	for a1 in [Ceiling(-6*sqrt_q)..Floor(6*sqrt_q)] do
		if (a1 mod q) ne Coeffs[6] then
			continue a1;	// value of a1 mod p
		end if;
		print "a1 =", a1;
	
		LB2 := Ceiling(4*sqrt_q*Abs(a1) - 9*q);
		UB2 := Floor(a1^2/3 + 3*q);
		
		print "Trying", #[Floor(LB2/q)-1..Ceiling(UB2/q)+1], "values for a2";
			
		for a2_divq in [Floor(LB2/q)-1..Ceiling(UB2/q)+1] do
			a2 := a2_divq*q + Coeffs[5];
			assert (a2 mod q) eq Coeffs[5];
			if (a2 lt LB2) or (a2 gt UB2) then
				continue a2_divq;
			end if;
			print "a2 =", a2;
		
			LB3 := Ceiling(Max(-2*q*a1-2*sqrt_q*a2-2*q*sqrt_q, -2*a1^3/27+a1*a2/3+q*a1-2/27*(a1^2-3*a2+9*q)^(3/2)));
			UB3 := Floor(Min(-2*q*a1+2*sqrt_q*a2+2*q*sqrt_q, -2*a1^3/27+a1*a2/3+q*a1+2/27*(a1^2-3*a2+9*q)^(3/2)));
			WeilPolynomial := RZ![q^3, q^2*a1, q*a2, 0, a2, a1, 1];
			OrderSoFar := Evaluate(WeilPolynomial, 1);
			
			r := Coeffs[4] mod q;
			// a3 must be r mod q
			print "Trying", #[Floor(LB3/q)-1..Ceiling(UB3/q)+1], "values for a3";

		
			for a3_divq in [Floor(LB3/q)-1..Ceiling(UB3/q)+1] do
				a3 := q*a3_divq + r;
				assert (a3 mod q) eq Coeffs[4];
				if (a3 lt LB3) or (a3 gt UB3) then
					continue a3_divq;
				end if;	
			
				n := OrderSoFar + a3;
				assert(n ne 0);
			
				if not(n in PotentialOrders) then
					Append(~PotentialOrders, n);
				end if;
			end for;
		end for;
	end for;
	Sort(~PotentialOrders);
	print #PotentialOrders, "potential orders found";

	StepSize := Ceiling(Sqrt(#PotentialOrders)); // Baby-step-giant-step size
	BigSteps := [PotentialOrders[1]];
	for i in [2..#PotentialOrders] do
		if PotentialOrders[i] ge BigSteps[#BigSteps] + StepSize*q then
			Append(~BigSteps, PotentialOrders[i]);
		end if;
	end for;
	print #BigSteps, "big steps found for baby-step-giant-step";
	
	
	Tries := 0;

	repeat
		Tries +:= 1;
		assert(Tries lt 20); // If this fails too often, just try another prime.
		Pt := Random(J);
		Found := 0;
		Success := true;
		qPt := q*Pt;
		
		// baby steps
		CurrentSmallMultiple := Zero(J);
		SmallMultiples := [CurrentSmallMultiple];
		for i in [1..StepSize-1] do
			CurrentSmallMultiple -:= qPt;
			if CurrentSmallMultiple in SmallMultiples then
				print "Baby steps failed";
				Success := false;
				break;
			end if;
			Append(~SmallMultiples, CurrentSmallMultiple);
		end for;
		if not(Success) then
			continue;
		end if;
		print "Baby steps finished";
		
		// giant steps
		OrderFound := -1;
		CurrentBigMultiple := BigSteps[1]*Pt;
		if CurrentBigMultiple in SmallMultiples then
			OrderFound := BigSteps[1] + 1 - Index(SmallMultiples, CurrentBigMultiple);
		end if;
		for i in [2..#BigSteps] do
			CurrentBigMultiple +:= Integers()! ( (BigSteps[i] - BigSteps[i-1])/q )*qPt;
			if CurrentBigMultiple in SmallMultiples then
				if OrderFound ne -1 then
					Success := false;
					break;
				end if;
				OrderFound := BigSteps[i] + q*(Index(SmallMultiples, CurrentBigMultiple) - 1);
			end if;
		end for;
		if not(Success) or (OrderFound eq -1) then
			print "Giant steps failed";
			Success := false;
			continue;
		end if;
		print "Giant steps finished";
		
		assert(OrderFound*Pt eq Zero(J));
	until Success;	

	print "Order at", q, "seems to be", OrderFound;
	J`Order := OrderFound;
end procedure;		

// MAIN FUNCTION

intrinsic TorsionSubgroup(J : SmallPrimes := PrimesInInterval(3,200), BigPrimes := PrimesInInterval(10^6, 10^6+600), MaxGroupSize := 1500, MaxNumberOfReconstructions := 2000, Heuristic := false)->SetEnum
{Function that attempts to compute the torsion subgroup of J. Input are:
* a set of small primes used for proving the completeness,
* a set of big primes used for the CRT reconstruction method of finding torsion points,
* the maximum size of the l-Sylow groups that will be considered in the algorithm,
* the maximum number of steps taken in the CRT reconstruction step
* a flag to call for the heuristic version of the algorithm that does not attempt to prove the output is correct.}
	
	// Step 0: initialise
	SmallPrimes := [p : p in SmallPrimes | not(p in BadPrimes(J`C)) and (p ne 2)];
	BigPrimes := [p : p in BigPrimes | not(p in BadPrimes(J`C)) and (p ne 2)];
	ProofPoints := {};
	TorsionGroup := {Zero(J)};
	Jp := AssociativeArray();
	Jp_big := [ Reduction(J, p) : p in BigPrimes];
	for p in SmallPrimes cat BigPrimes do
			Jp[p] := Reduction(J, p);
	end for;
	Points_Jp := AssociativeArray();
	lTorsion_p := AssociativeArray();
	lDivCandidates_p := AssociativeArray();
	assert(#SmallPrimes ne 0);
	assert(#BigPrimes ne 0);
	
	// Step 0.5: finding orders of Jacobians for small primes
	OrderMissing := [p : p in SmallPrimes | Jp[p]`Order eq 0];
	FrobPolyList := FrobeniusPolynomial(Polynomial(J`C), OrderMissing);
	for i in [1..#OrderMissing] do
		Jp[OrderMissing[i]]`Order := Evaluate(FrobPolyList[i], 1);
	end for;
	print "Step 0.5: necessary Frobenius polynomials computed";
	
	
	// Step 1: find some upper bound
	UB := 0;
	for p in SmallPrimes do
		UB := GCD(UB, Order(Jp[p]));
	end for;
	ProofPrimes := {Min(SmallPrimes)};
	for l in PrimeDivisors(Order(Jp[Min(SmallPrimes)])) do
		for p in SmallPrimes do
			if Valuation(Order(Jp[p]), l) eq Valuation(UB, l) then
				Include(~ProofPrimes, p);
				continue l;
			end if;
		end for;
		assert(false); // This would mean something is fishy about the upper bound.
	end for;
	print "Step 1: initial upper bound", UB;
	if UB eq 1 then
		return TorsionGroup, ProofPrimes, ProofPoints;
	end if;
	
	// Step 1.1: finding order of Jacobians for big primes
	OrderMissing := [p : p in BigPrimes | Jp[p]`Order eq 0];
	FrobPolyList := FrobeniusPolynomial(Polynomial(J`C), OrderMissing);
	for i in [1..#OrderMissing] do
		try
			GuessOrder(Jp[OrderMissing[i]], FrobPolyList[i]);
		catch e // Happens if middle coefficient is divisible by p
			print "Failed to compute order at prime", OrderMissing[i];
			Exclude(~BigPrimes, OrderMissing[i]);
		end try;
	end for;
	print "Step 0.5: necessary Frobenius polynomials computed";
	
	// Step 1.2: main algorithm
	for l in Reverse(PrimeDivisors(UB)) do
		MaxGroupSize_l := MaxGroupSize;
		Primes_l := [p : p in SmallPrimes cat BigPrimes | l^Valuation(Order(Jp[p]), l) lt MaxGroupSize];
		while (#Primes_l eq 0) do
			MaxGroupSize_l *:= l;
			Primes_l := [p : p in SmallPrimes cat BigPrimes | l^Valuation(Order(Jp[p]), l) lt MaxGroupSize_l];
		end while;
		BigPrimes_l := [p : p in Primes_l | p in BigPrimes];
		SmallPrimes_l := [p : p in Primes_l | p in SmallPrimes];
		lTorsionOverClosure := {};	// All non-zero l-torsion points found over algebraic closure
		B := Max(Primes_l);
		if (B lt 1000) then
			if Heuristic eq false then
				return {}, {}, {}; // Abandon attempt.
			end if;
		end if;
		lTorsionOverClosure_B := {}; // Their reductions module a big prime
		lTorsion := {Zero(J)};		// Just points over the right base field
		Status := AssociativeArray();	// Status: 0 (point found), 1 (rational reconstruction attempt done), 2 (point not divisible anymore)
		Status[Zero(J)] := 0;	
		SylowTime := -Cputime();
		for p in Primes_l do
			Points_Jp[p] := pSylowSubgroup(Jp[p], l);
			lTorsion_p[p] := {Zero(Jp[p])};
		end for;
		SylowTime +:= Cputime();
		print SylowTime, "seconds spend on computing Sylow-subgroups modulo primes";

		
		while (#[Pt : Pt in lTorsion | Status[Pt] ne 2] gt 0) and (#lTorsion lt l^Valuation(UB,l)) do
			SomethingChanged := false;
		
			// Step 2: check for points which are not divisible anymore
			for Pt in [Pt : Pt in lTorsion | Status[Pt] ne 2] do
				print "Considering point", Pt;
				if Status[Pt] eq 2 then
					continue Pt;
				end if;
				
				// Step 2a: easy check to see if point can be removed from list
				for p in SmallPrimes_l do
					try
						Pt_red := UniqueElement(PrimeReduction(J, Pt, p));
					catch e
						continue p;
					end try;
					lDivCandidates_p[p] := {Pt_p : Pt_p in Points_Jp[p] | l*Pt_p eq Pt_red };
					if lDivCandidates_p[p] subset lTorsion_p[p] then
						for Q in lTorsion do
							for m in [1..l-1] do
								Status[m*Pt + l*Q] := 2;
							end for;
						end for;
						print "Point", Pt, "is not", l, "-divisible - step 2a", p;
						Include(~ProofPrimes, p);
						SomethingChanged := true;
						continue Pt;
					end if;
				end for;	
				print "Finished step 2a";
											
				// Step 2b: add new points
				if Status[Pt] in {0,3} then
					PotentialDivisors := DivisionByRationalReconstruction(J, Pt, l, BigPrimes_l : JpList := [Jp[p] : p in BigPrimes_l], MaxDegree := 4, lTorsion := {Pt : Pt in lTorsion | l*Pt eq 0}, ExtraPrimes := SmallPrimes_l, MaxNumberOfReconstructions := MaxNumberOfReconstructions);
					if (#PotentialDivisors eq 0) or (Status[Pt] eq 3) then
						if Max(BigPrimes) gt 10^6 + 1000 then
							//assert(l le 3);
							if l lt 4 and Heuristic eq false then
								PotentialDivisors := AnalyticDivision(J`C, J, Pt, l, lTorsion);
							else
								print "The prime", l, "failed, abort attempt";
							end if;
							//assert(#PotentialDivisors ne 0);
						end if;
						if #PotentialDivisors eq 0 and Max(BigPrimes) lt 10^6 + 1000 then
							if Heuristic eq false then				
								return {}, {}, {}; // Abandon try
							end if;
						end if;
					end if;
					print "Potential l-divisors found";
					
					for NewPt in PotentialDivisors do
						if (BaseField(NewPt`J`C) eq BaseField(J`C)) and not(NewPt in lTorsion) then
							print "New", l, "-torsion point found:", NewPt;
							SomethingChanged := true;
							AddElementToSubgroup(~lTorsion, NewPt);
							for p in Primes_l do
								AddElementToSubgroup(~lTorsion_p[p], UniqueElement(PrimeReduction(J, NewPt, p)));
							end for;
							for Pt2 in lTorsion do
								if Pt2 in Keys(Status) and Status[Pt2] eq 2 then
									for Pt3 in lTorsion do
										Status[Pt2 + l*Pt3] := 2;
									end for;
								end if;
							end for;
						end if;
					end for;
					
					for NewPt in PotentialDivisors do
						if BaseField(NewPt`J`C) ne BaseField(J`C) then
							NewPtB := PrimeReduction(J, NewPt, B);
							if NewPtB in lTorsionOverClosure_B then
								print "Algebraic point was already listed1";
								continue NewPt;
							end if;
							for T in lTorsionOverClosure join {[Zero(J), Zero(J)]} do
								if T[2] eq 0 then
									for x in MyPlus(J, T[1], NewPt) do
										xB := PrimeReduction(J, x, B);
										if xB in lTorsionOverClosure_B then
											print "Algebraic point was already listed2";
											continue x;
										end if;
										for y in [z : z in lTorsion_p[B] | l*z eq 0] do
											xB_plus_y := { UniqueElement(MyPlus(J, y, z)) : z in xB };
											Include(~lTorsionOverClosure_B, xB_plus_y);
										end for;										
										Include(~lTorsionOverClosure, [x, Pt]);	// Keep track of both the new point and l*new point
										print "New algebraic point added";
										//assert(#lTorsionOverClosure eq #lTorsionOverClosure_B);
									end for;
								end if;
							end for;
						end if;
					end for;
					if Status[Pt] in {0,3} then
						Status[Pt] +:= 1;
					end if;
					print "Finished step 2b";
				else
					print "Skipped step 2b";
				end if;
				
					
				// Step 2c: extensive check if point can be removed from list
				for p in SmallPrimes_l do
					print "Trying prime", p;
					
					// Repeat the easy check, just in case a new point has been found in step 2b.
					if lDivCandidates_p[p] subset lTorsion_p[p] then
						for Q in lTorsion do
							for m in [1..l-1] do
								Status[m*Pt + l*Q] := 2;
							end for;
						end for;
						print "Point", Pt, "is not", l, "-divisible - step 2c1", p;
						Include(~ProofPrimes, p);
						SomethingChanged := true;
						continue Pt;
					end if;
										
					// Now also check reductions of non-rational points
					lDivCandFound_p := lTorsion_p[p] meet lDivCandidates_p[p];
					PotentialProofPoints := {};
					for AlgPt in lTorsionOverClosure do
						if AlgPt[2] ne Pt then
							continue AlgPt;	// Check if AlgPt is an l-divisor of Pt
						elif AbsoluteDegree(BaseField(AlgPt[1]`J`C)) ge p then
							continue AlgPt; // Injectivity is not guaranteed in this case
						end if;
												
						// Reduce AlgPt modulo p
						K := BaseField(AlgPt[1]`J`C);
						if K eq Rationals() then
							try
								AlgPt_p := UniqueElement(PrimeReduction(J, AlgPt[1], p));
								if not(AlgPt_p in lDivCandFound_p) then
									Include(~lDivCandFound_p, AlgPt_p);
									Include(~PotentialProofPoints, AlgPt[1]);
								end if;
							catch e
								continue p;
							end try;
							continue AlgPt;
						end if;
						
						try 
							AlgPt_p_list := PrimeReduction(J, AlgPt[1], p);
						catch e
							continue AlgPt;
						end try;
						for AlgPt_p in AlgPt_p_list do
							if #BaseField(AlgPt_p`J`C) ne p then
								continue AlgPt_p;
							end if;
							assert AlgPt_p in lDivCandidates_p[p];
							if not(AlgPt_p in lDivCandFound_p) then
								Include(~PotentialProofPoints, AlgPt[1]);
								for Q in lTorsion_p[p] do
									if l*Q eq 0 then
										Include(~lDivCandFound_p, AlgPt_p + Q);
									end if;
								end for;
								if #lDivCandidates_p[p] eq #lDivCandFound_p then
									break AlgPt;
								end if;
							end if;
							print "At prime", p, "point", Decomposition(InputRepresentations(AlgPt_p)[1]), "can be explained";
						end for; // end for AlgPt_p
						
						//end for; // end for T
						
					end for; // end for AlgPt
					//MakeSubgroup(~lDivCandFound_p, ~lDivCandFound_p);
					
					if lDivCandidates_p[p] eq lDivCandFound_p then
						for Q in lTorsion do
							for m in [1..l-1] do
								Status[m*Pt + l*Q] := 2;
							end for;
						end for;
						print "Point", Pt, "is not", l, "-divisible - step 2c2", p;
						Include(~ProofPrimes, p);
						ProofPoints := ProofPoints join PotentialProofPoints;
						SomethingChanged := true;
						continue Pt;
					end if;
				end for;
				print "Finished step 2c";
			end for;
			

			if Max(BigPrimes) gt 10^6 + 1000 then
				for Pt in Keys(Status) do
					if Status[Pt] eq 1 then
						SomethingChanged := true;
						Status[Pt] := 3;
					end if;
				end for;
				//assert(SomethingChanged);
			end if;

			if not(SomethingChanged) then	
				print "Nothing changed for prime", l;	
				if Heuristic eq false then		
					return {}, {}, {};
				else
					break;
				end if;
			end if;
			// Update status
			for Pt in lTorsion do
				if not(Pt in Keys(Status)) then
					Status[Pt] := 0;
				end if;
			end for;	
		end while;
		
		print l,"-torsion found";		
		for p in lTorsion do
			AddElementToSubgroup(~TorsionGroup, p);
		end for;		
	end for;
	
	return TorsionGroup, ProofPrimes, ProofPoints;
end intrinsic;

intrinsic Torsion(C : SkipFirstThree := false, CatchError := false, Heuristic := false)->SetEnum
{Wrapper function to try to compute the torsion of a plane quartic curve.}
	if SkipFirstThree then
		Primes := [ [* PrimesInInterval(3,300),PrimesInInterval(10^6, 10^6 + 1200), 10000 *] ];
		//T, a, b := TorsionSubgroup(J : SmallPrimes := P[1], BigPrimes := P[2], MaxNumberOfReconstructions := P[3]);
		//return T, a, b;
	elif Heuristic then
		Primes := [ [* PrimesInInterval(3,200),PrimesInInterval(10^4, 10^4 + 300), 2000 *] ];
	else
		Primes := [ [* PrimesInInterval(3,100),PrimesInInterval(10^4, 10^4+100), 2000 *] , [* PrimesInInterval(3,200),PrimesInInterval(10^4, 10^4 + 300), 2000 *], [* PrimesInInterval(3,300),PrimesInInterval(10^6, 10^6 + 600), 10000 *], [* PrimesInInterval(3,300),PrimesInInterval(10^6, 10^6 + 1200), 10000 *] ];
	end if;
	
	Pts_sorted := Sort([x : x in Points(C : Bound := 100)], IsSimpler);
	Pts_sorted2 := Sort([x : x in Points(C : Bound := 100)], IsSimpler);
	if (#Pts_sorted2 gt #Pts_sorted) then
		Pts_sorted := Pts_sorted2;
	end if;
	SavedOrders := [];
	print Pts_sorted;
	
	for Pt in Pts_sorted do
		J := GenericJacobian(C, Divisor(Pt));
		for L in SavedOrders do
			Jp := Reduction(J, L[1]);
			Jp`Order := L[2];
		end for;
		
		for P in Primes do
			if CatchError eq false then
				T, a, b := TorsionSubgroup(J : SmallPrimes := P[1], BigPrimes := P[2], MaxNumberOfReconstructions := P[3], Heuristic := Heuristic);
					if a eq {} then
						print "Attempt failed, retrying with bigger primes (at most three times)";
						continue P;
					end if;
					return J, T, a, b;
			else				
				try
					T, a, b := TorsionSubgroup(J : SmallPrimes := P[1], BigPrimes := P[2], MaxNumberOfReconstructions := P[3], Heuristic := Heuristic);
					if a eq {} then
						print "Attempt failed, retrying with bigger primes (at most three times)";
						continue P;
					end if;
					return J, T, a, b;
				catch e
					print e;
					break P;
				end try;
			end if;
		end for;
		
		SavedOrders := [];
		for p in Keys(J`ReductionObj) do
			Jp := Reduction(J, p);
			if Jp`Order ne 0 then
				Append(~SavedOrders, [p, Jp`Order]);
			end if;
		end for;
		
	end for;
	assert(false); // Failed
end intrinsic;

function MyPairing(D, E, n)
	assert(Degree(D) eq 0);
	assert(Degree(E) eq 0);
	assert(Dimension(n*D) eq 1);
	assert(Dimension(n*E) eq 1);
	f := Basis(n*D)[1];
	g := Basis(n*E)[1];
	S := Set(Support(D)) join Set(Support(E));
	PairingValue := 1;
	for P in S do
		OrdD := Valuation(D, P);
		OrdE := Valuation(E, P);
		FunctionValue := Evaluate( g^OrdD / f^OrdE, P );
		if Degree(P) gt 1 then
			FunctionValue := Norm(FunctionValue);
		end if;
		PairingValue *:= (-1)^(n*OrdD*OrdE) * FunctionValue;
	end for;
	return PairingValue;
end function;

function IsRational(J, Pt)
	K := BaseField(PointOverSmallestField(J, Pt)`J`C);
	if IsPrimeField(K) then
		return true;
	else
		return false;
	end if;
	L, rts := NormalClosure(K);
	phi := hom<K->L | rts[1]>;
	JL, rho := BaseChange(Pt`J, phi);
	PtL := BaseChange(Pt, JL, rho);
	GalL, AutL, phiL := AutomorphismGroup(L);
	for sigma in GalL do
		rhoL := phiL(sigma);
		Pt_sigma := ApplyAutomorphism(PtL, rhoL);
		if PtL ne Pt_sigma then
			return false;
		end if;
	end for;
	return true;
end function;

intrinsic ConvertProofToList(J, T, ProofPrimes, ProofPoints)->List
{Convert proof data to list for storage purposes.}
	JL := IntegerList(J);
	TL := [ IntegerList(Pt) : Pt in T ];
	ProofPointsL := [ IntegerList(Pt) : Pt in ProofPoints ];
	return [* JL, TL, ProofPrimes, ProofPointsL *];
end intrinsic;

intrinsic ConvertListToProof(L::List)->JacCrv, SeqEnum, SeqEnum, SeqEnum
{Convert list proof data to mathematical objects.}
	J := GenericJacobian(L[1]);
	T := [Point(J, x) : x in L[2]];
	ProofPoints := [Point(J, x) : x in L[4]];
	return J, T, L[3], ProofPoints;
end intrinsic;

intrinsic VerifyProof(J::JacCrv, T, ProofPrimes, ProofPoints)->BoolElt
{Verify proof of torsion computation. Input are the Jacobian, the torsion points found, a set of primes used in the proof, and a set of points over a number field used in the proof.}

	Jp := AssociativeArray();
	for p in ProofPrimes do
		Jp[p] := Reduction(J, p);
	end for;
	for Pt in ProofPoints do
		if IsRational(J, Pt) then
			return false; // ProofPoints have to be non-rational
		end if;
	end for;

	// Step 1: finding orders of reduction of Jacobians
	UB := 0;
	for p in ProofPrimes do
		print "Order of reduction mod", p, "equals", Order(Jp[p]);
		UB := GCD(UB, Order(Jp[p]));
	end for;
	print "Found the upper bound", UB, "for the torsion";
	
	// Step 2: verifying the divisibility of each point
	for l in PrimeDivisors(UB) do
		lProofPoints := [ Q : Q in ProofPoints | Order(Q) mod l eq 0 ];
		lTorsion := { P : P in T | IsDivisibleBy(l^Valuation(UB,l), Order(P)) };
		ProofPointsL := &join[ &join[ &join[MyPlus(J, P, i*Q) : i in [1..l-1] ]: Q in lProofPoints] : P in lTorsion ];
		print "T contains", #lTorsion, "points of", l, "-power order";
		
		if Valuation(#lTorsion, l) eq Valuation(UB, l) then
			print "The upper bound is already tight. Proceed to next prime.";
			continue l;
		else
			print "The upper bound is not tight yet. Proceed to check for divisibility.";
		end if;
	
		lTorsion_p := AssociativeArray();
		for p in ProofPrimes do
			lTorsion_p[p] := pSylowSubgroup(Jp[p], l);
		end for;	
		for P in lTorsion do
		
			lDivisorsOfP := { Q : Q in lTorsion | l*Q eq P };
			lDivisorsOfP_p := AssociativeArray();
		
			// Step 2a: first try plain reduction
			for p in ProofPrimes do
				try
					P_p := UniqueElement(PrimeReduction(J, P, p));	
					lDivisorsOfP_p[p] := { Q : Q in lTorsion_p[p] | l*Q eq P_p };
					if #lDivisorsOfP_p[p] eq #lDivisorsOfP then
						Decomposition_P := Decomposition(P`D);
						print "The point", P, "given by", P`D, "does not have more", l, "-divisors modulo", p;
						print #lDivisorsOfP_p[p], #lDivisorsOfP;
						continue P;
					end if;
				catch e
					continue p; // skip primes for which the reduction cannot be computed
				end try;
			end for;
			
			// Step 2b: try with extra points
			for Q in ProofPointsL do
				if not(MyEq(l*Q, P)) then
					print "Point skipped";
					continue Q;
				end if;
				for p in ProofPrimes do
					try
						for Q_p in PrimeReduction(J, Q, p) do
							if Q_p in lDivisorsOfP_p[p] then
								Exclude(~lDivisorsOfP_p[p], Q_p);
								print "Removed image of non-rational point in the potential list mod", p;
								if #lDivisorsOfP_p[p] eq #lDivisorsOfP then
									print "After adjoining non-algebraic points, the", l, "-divisors of", P, "can be explained.";
									continue P;
								end if;
							end if;
						end for;
				
					catch e
						print "Prime", p, "failed";
						print e;
						continue p; // skip primes for which the reduction cannot be computed
					end try;
				end for;
			end for;
			
			return false;		
		end for;	
	end for;
	

	return true;
end intrinsic;

intrinsic VerifyListProof(L::List)->BoolElt
{Verify proof stored in list form.}
	J, T, a, b := ConvertListToProof(L);
	return VerifyProof(J, T, a, b);
end intrinsic;
