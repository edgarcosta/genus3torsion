// This implements algebraic Jacobian arithmetic in a naive way

declare type JacCrv;
declare attributes JacCrv: C, D_def, ReductionObj, ReductionDivMap, Order, D_can, Hash, pSylowSubgroup;
declare type JacCrvPt;
declare attributes JacCrvPt: J, D, Order, CanonicalRepresentations, Hash, Multiples, Ideal;

intrinsic BadPrimes(C::Crv)->SetEnum
{Find a superset of the bad primes for C.}
	require IsProjective(Ambient(C)) : "Ambient space of C has to be P2";
	require Dimension(Ambient(C)) eq 2: "Ambient space of C has to be P2";
	f := Equation(C);
	RZ<xZ,yZ,zZ> := PolynomialRing(Integers(),3);
	den := LCM([Denominator(c) : c in Coefficients(f)]);
	f := RZ!(den*f);
	fx := Derivative(f, xZ);
	fy := Derivative(f, yZ);
	fz := Derivative(f, zZ);
	
	NaiveDiscriminant := 1;
	for P in [ [xZ, yZ, 1], [xZ, 1, zZ], [1, yZ, zZ] ] do
		I := Ideal([ Evaluate(g, P) : g in [f, fx, fy, fz]]);
		G := GroebnerBasis(I);
		PotentialDiscriminant := G[#G];
		assert(PotentialDiscriminant in Integers());
		NaiveDiscriminant := LCM(NaiveDiscriminant, PotentialDiscriminant);
	end for;
	
	return Set(PrimeFactors(Integers()!NaiveDiscriminant));
end intrinsic;

intrinsic Print(J::JacCrv){}
	printf "Jacobian of %o ", J`C;
	printf "using divisor %o to define points", J`D_def;
end intrinsic;

intrinsic ActualJacobianPoint(Pt::JacCrvPt)->DivCrvElt{}
	n := Integers()!(Degree(Pt`D)/Degree(Pt`J`D_can));
	return Pt`D - n*Pt`J`D_can;
end intrinsic;

intrinsic Print(Pt::JacCrvPt){}
	printf "Point defined by %o ", ActualJacobianPoint(Pt);
	printf "on %o", Pt`J;
end intrinsic;

function DegreeOneDivisor(C)
	if IsFinite(BaseField(C)) then
		F<x> := FunctionField(C);
		for c in BaseField(C) do
			D := Divisor(C, x-c);
			for Pl in Decomposition(D) do
				if Degree(Pl[1]) eq 1 then
					return true, Divisor(Pl[1]);
				end if;
			end for;
		end for;
		return false, 0;
	else
		PtsC := Points(C : Bound := 100);
		if #PtsC gt 0 then
			for Pt in PtsC do
				return true, Divisor(Pt);
			end for;
		else
			return false, 0;
		end if;
	end if;
end function;

intrinsic GenericJacobian(C::Crv, D::DivCrvElt)->JacCrv
{New Jacobian creation}
	require IsNonSingular(C) : "Curve must be non-singular";
	J := New(JacCrv);
	J`C := C;
	J`D_def := D;
	if Degree(D) eq 1 then
		J`D_can := D;
	else
		found, D_can := DegreeOneDivisor(C);
		if found then
			J`D_can := D_can;
		else
			J`D_can := D;
		end if;
	end if;
	J`Order := 0;
	J`ReductionObj := AssociativeArray();
	J`ReductionDivMap := AssociativeArray();
	J`pSylowSubgroup := AssociativeArray();
	return J;
end intrinsic;

intrinsic GenericJacobian(C::Crv)->JacCrv
{New Jacobian creation}
	require IsNonSingular(C) : "Curve must be non-singular";
	found, D_can := DegreeOneDivisor(C);
	require found : "Degree one divisor could not be found";
	return GenericJacobian(C, D_can);
end intrinsic;

intrinsic Point(J::JacCrv, D::DivCrvElt)->JacCrvPt
{New point creation}
	Pt := New(JacCrvPt);
	Pt`J := J;
	require Degree(D) mod Degree(J`D_def) eq 0: "Divisor degree must be multiple of ", Degree(J`D_def);
	n := Integers()!(Degree(D)/Degree(J`D_def));
	Pt`D := Reduction(D - n*J`D_def , J`D_can);
	Pt`Order := 0;
	Pt`Multiples := AssociativeArray();
	return Pt;
end intrinsic;

function InternalPoint(J,D : ComputeHash := true);
// Internal point creation using D_can
	Pt := New(JacCrvPt);
	Pt`J := J;
	Pt`D := Reduction(D, J`D_can);
	Pt`Order := 0;
	Pt`Multiples := AssociativeArray();
	if Degree(J`D_can) eq 1 then
		if ComputeHash then
			Pt`Hash := Hash(J) + 3417*Hash(Decomposition(Pt`D));
		else
			Pt`CanonicalRepresentations := [Pt`D];
		end if;
	end if;
	return Pt;
end function;

intrinsic Zero(J::JacCrv)->JacCrvPt
{Creation of zero}
	D := DivisorGroup(J`C)!0;
	return InternalPoint(J, D);
end intrinsic;

intrinsic 'eq'(J1::JacCrv, J2::JacCrv)->BoolElt {}
	if Hash(J1) ne Hash(J2) then
		return false;
	elif (J1`C eq J2`C) and (J1`D_def eq J2`D_def) then
		return true;
	else
		return false;
	end if;
end intrinsic;

intrinsic 'eq'(Pt1::JacCrvPt, Pt2::JacCrvPt)->BoolElt {}
	if Hash(Pt1) ne Hash(Pt2) then
		return false;
	end if;
	IsEquiv := IsLinearlyEquivalent(Pt1`D, Pt2`D);
	return IsEquiv;
end intrinsic;

intrinsic 'eq'(Pt::JacCrvPt, zero::RngIntElt)->BoolElt {}
	require zero eq 0: "Jacobian point can only be compared with zero";
	IsZero := IsPrincipal(Pt`D);
	return IsZero;
end intrinsic;

function InternalPlus(Pt1, Pt2)
//{Computes the sum without computing the hash.}
	return InternalPoint(Pt1`J, Pt1`D+Pt2`D : ComputeHash := false);
end function;

intrinsic '+'(Pt1::JacCrvPt, Pt2::JacCrvPt)->JacCrvPt
{Addition of points}
	require Pt1`J eq Pt2`J : "Points must be defined on the same Jacobian";
	return InternalPoint(Pt1`J, Pt1`D+Pt2`D);
end intrinsic;

intrinsic '-'(Pt1::JacCrvPt, Pt2::JacCrvPt)->JacCrvPt
{Addition of points}
	require Pt1`J eq Pt2`J : "Points must be defined on the same Jacobian";
	return InternalPoint(Pt1`J, Pt1`D-Pt2`D);
end intrinsic;

intrinsic '-'(Pt::JacCrvPt)->JacCrvPt
{Negative of a point}
	return InternalPoint(Pt`J, -Pt`D);
end intrinsic;

function MultPoint(n, Pt)
	if Pt`Order ne 0 then
		n mod:= Pt`Order;
	end if;
	if (n lt 0) then
		return -MultPoint(-n, Pt);
	elif (n eq 0) then
		return Zero(Pt`J);
	elif (n eq 1) then
		return Pt;
	elif (n mod 2 eq 0) then
		Pt2 := MultPoint(n div 2, Pt);
		return InternalPlus(Pt2, Pt2);
	else 
		Pt2 := MultPoint(n div 2, Pt);
		return InternalPlus(InternalPlus(Pt2, Pt2), Pt);
	end if;
end function;

intrinsic '*'(n::RngIntElt, Pt::JacCrvPt)->JacCrvPt
{Scalar multiplication}
	if not(n in Keys(Pt`Multiples)) then
		Pt2 := MultPoint(n, Pt);
		if Pt2 eq 0 then
			Pt`Order := GCD(Pt`Order, n);
		end if;
		if Pt`Order ne 0 then
			Pt2`Order := Integers()!(Pt`Order/GCD(Pt`Order,n));
		end if;
		Pt`Multiples[n] := Pt2;
	end if;
	return Pt`Multiples[n];
end intrinsic;

intrinsic AllRepresentations(Pt::JacCrvPt)->SeqEnum
{All representations of a point on the Jacobian}
	D := Reduction(ActualJacobianPoint(Pt), Pt`J`D_def);
	B := Basis(D);
	if #B eq 1 then
		return [Pt`D];
	end if;
	require IsFinite(BaseRing(Pt`J`C)) : "Representation is non-unique: all representations can only be listed when working over finite fields";
	return [ D + Divisor(&+[c[i]*B[i] : i in [1..#B]]) : c in Points(ProjectiveSpace(BaseRing(Pt`J`C), #B-1)) ];	
end intrinsic;


intrinsic CanonicalRepresentations(Pt::JacCrvPt)->JacCrvPt
{Canonical representations of a point. Requires setting a effective degree 1 divisor.}
	if not(assigned(Pt`CanonicalRepresentations)) then
		B := Basis(Pt`D);
		if #B eq 1 then
			Pt`CanonicalRepresentations := [Pt`D];
		elif IsFinite(BaseRing(Pt`J`C)) then	// This should only happen for small rings, otherwise there is a degree 1 divisor
			Pt`CanonicalRepresentations := [ Pt`D + Divisor(&+[c[i]*B[i] : i in [1..#B]]) : c in Points(ProjectiveSpace(BaseRing(Pt`J`C), #B-1)) ];
		else
			Pt`CanonicalRepresentations := [];
		end if;
	end if;
	return Pt`CanonicalRepresentations;
end intrinsic;

intrinsic Ideal(Pt::JacCrvPt)->SeqEnum
{Ideal representing the point.}
	if not(assigned(Pt`Ideal)) then
		if Pt`J`D_can eq Pt`J`D_def then
			D := Pt`D;
		else
			D := Reduction(ActualJacobianPoint(Pt), Pt`J`D_def);
		end if;
		Pt`Ideal := Ideal(D);	
	end if;
	return Pt`Ideal;
end intrinsic;

function ReconstructPolynomial(R, coeffs, monoms)
	assert(#coeffs eq #monoms);
	pol := R!0;
	K := BaseRing(R);
	for i in [1..#coeffs] do
		ci := K!coeffs[i];
		mi := &*[ R.j^monoms[i][j] : j in [ 1..#monoms[i] ] ];
		pol +:= ci * mi;
	end for;
	return pol;
end function;

intrinsic GenericJacobian(L::List)->JacCrv
{Construct Jacobian from list.}
	P2<x,y,z> := ProjectiveSpace(Rationals(), 2);
	R := CoordinateRing(P2);
	eqn := ReconstructPolynomial(R, L[1], L[2]);
	C := Curve(P2, eqn);
	
	gens_num := [];
	assert(#L[3] eq #L[4]);
	for i in [1..#L[3]] do
		poli := ReconstructPolynomial(R, L[3][i], L[4][i]);
		Append(~gens_num, poli);
	end for;
	Inum := ideal< R | gens_num >;
	Dnum := Divisor(C, Inum);	
	
	gens_den := [];
	assert(#L[5] eq #L[6]);
	for i in [1..#L[5]] do
		poli := ReconstructPolynomial(R, L[5][i], L[6][i]);
		Append(~gens_den, poli);
	end for;
	Iden := ideal< R | gens_den >;
	Dden := Divisor(C, Iden);
	
	J := GenericJacobian(C, Dnum - Dden);
	return J;
	
end intrinsic;

intrinsic Point(J::JacCrv, L::List)->JacCrvPt
{Construct Jacobian point from list.}
	require BaseField(J`C) eq Rationals(): "Jacobian must be defined over rationals.";
	S<x> := PolynomialRing(Rationals());
	f := S!L[1];
	K := NumberField(f);
	JK := BaseChange(J, hom<Rationals()->K |>);
	R<x,y,z> := CoordinateRing(Ambient(JK`C));
	
	gens := [];
	assert(#L[2] eq #L[3]);
	for i in [1..#L[2]] do
		poli := ReconstructPolynomial(R, L[2][i], L[3][i]);
		Append(~gens, poli);
	end for;
	I := ideal<R | gens>;
	D := Divisor(JK`C, I);
	Pt := Point(JK, D);
	Pt`Ideal := I;
	return Pt;
end intrinsic;

intrinsic List(J::JacCrv)->List
{Turn a Jacobian into a list of integers.}
	eqn := Equation(J`C);
	coeffs_eqn := [ Eltseq(c) : c in Coefficients(eqn)];
	monoms_eqn := [ Exponents(m) : m in Monomials(eqn)];
	D := J`D_def;
	Dnum := Numerator(D);
	Dden := Denominator(D);
	Inum := Ideal(Dnum);
	Iden := Ideal(Dden);
	Bnum := Generators(Inum);
	Bden := Generators(Iden);
	coeffs_Bnum := [ [Eltseq(c) : c in Coefficients(x)] : x in Bnum];
	monoms_Bnum := [ [ Exponents(m) : m in Monomials(x)] : x in Bnum];
	coeffs_Bden := [ [Eltseq(c) : c in Coefficients(x)] : x in Bden];
	monoms_Bden := [ [ Exponents(m) : m in Monomials(x)] : x in Bden];
	return [* coeffs_eqn, monoms_eqn, coeffs_Bnum, monoms_Bnum, coeffs_Bden, monoms_Bden *];
end intrinsic;

intrinsic List(Pt::JacCrvPt)->List
{Turn a point on a Jacobian into a list of integers.}
	I := Ideal(Pt);
	B := Generators(I);
	K := BaseRing(I);
	pol := DefiningPolynomial(K);
	coeffs_B := [ [ Eltseq(c) : c in Coefficients(x)] : x in B];
	monoms_B := [ [ Exponents(m) : m in Monomials(x)] : x in B];
	return [* Coefficients(pol), coeffs_B, monoms_B *];
end intrinsic;

intrinsic InputRepresentations(Pt::JacCrvPt)->SeqEnum
{All representations of a point on the Jacobian}
	D := Reduction(ActualJacobianPoint(Pt), Pt`J`D_def);
	if Dimension(D) eq 1 then
		return [D];
	else
		return [];
	end if;	
end intrinsic;

intrinsic Hash(J::JacCrv)->RngIntElt
{Hash of a Jacobian}
	if not(assigned(J`Hash)) then
		CurveHash := Hash(J`C);
		DivisorHash := Hash(Decomposition(J`D_def));
		CanRepHash := Hash(Decomposition(J`D_can));
		J`Hash := 10001*CurveHash+101*DivisorHash+CanRepHash;
	end if;
	return J`Hash;	
end intrinsic;

intrinsic Hash(Pt::JacCrvPt)->RngIntElt
{Hash of a Jacobian point}
	if not(assigned(Pt`Hash)) then
		JacobianHash := Hash(Pt`J);
		DivisorHash := 0;
		CanReps := CanonicalRepresentations(Pt);
		for D in CanonicalRepresentations(Pt) do
			DivisorHash +:= Hash(Decomposition(D));
		end for;
		Pt`Hash := JacobianHash + 3417*DivisorHash;
	end if;
	return Pt`Hash;
end intrinsic;

function NormalisedGenerators(I) // Normalised generators for ideal, assumes an implementation of the GCD in the base ring
	G := GroebnerBasis(I);
	try
	   GZ := [g*LCM([Denominator(c) : c in Coefficients(g)]) : g in G];
	   return [g/GCD([Numerator(c) : c in Coefficients(g)]) : g in GZ];
	catch e
	   return G; // If there is no GCD, just try the Groebner basis.
	end try;	   
end function;

intrinsic BaseChange(J::JacCrv, phi::Map)->JacCrv,Map
{Base change of Jacobian together with a map used to base change divisors}
	//if phi in Keys(J`BaseChangeObj) then
	//	return J`BaseChangeObj[phi];
	//end if;
	require Type(Domain(phi)) eq Type(BaseRing(J`C)) : "Curve must be defined over the domain of the map";
	require Domain(phi) eq BaseRing(J`C) : "Curve must be defined over the domain of the map";
	if IsIdentity(FieldMorphism(phi)) then
		rho := IdentityHomomorphism(CoordinateRing(Ambient(J`C)));
		return J, rho;
	end if;	
	Cphi := BaseChange(J`C, phi);
	I := Ideal(J`D_def);
	Aphi := CoordinateRing(Ambient(Cphi));
	if IsPrimeField(BaseRing(I^0)) then
		rho := hom<I^0->Aphi | [Aphi.i : i in [1..Rank(Aphi)]]>;
	else
		rho := hom<I^0->Aphi | phi, [Aphi.i : i in [1..Rank(Aphi)]]>;	
	end if;
	Iphi := ideal<Aphi | [rho(x) : x in NormalisedGenerators(I)]>;
	Dphi := Divisor(Cphi, Iphi);
	Jphi := GenericJacobian(Cphi, Dphi);	
	//J`BaseChangeObj[phi] := Jphi;
	//J`BaseChangeDivMap[phi] := rho;
	return Jphi, rho;
end intrinsic;

intrinsic ApplyAutomorphism(Pt::JacCrvPt, phi::Map)->JacCrvPt
{Apply automorphism to point on Jacobian}
	J := Pt`J;
	require Type(Domain(phi)) eq Type(BaseRing(J`C)) : "Curve must be defined over the domain of the map";
	require Type(Codomain(phi)) eq Type(BaseRing(J`C)) : "Curve must be defined over the codomain of the map";
	require Domain(phi) eq BaseRing(J`C) : "Curve must be defined over the domain of the map";
	require Domain(phi) eq Codomain(phi): "phi must be an automorphism";
	A := CoordinateRing(Ambient(J`C));
	rho := hom<A->A | phi, [A.i : i in [1..Rank(A)]]>;
	return BaseChange(Pt, J, rho);
end intrinsic;

intrinsic Reduction(J::JacCrv, p::RngIntElt)->JacCrv
{Reduction of Jacobian over Q mod p}
	if p in Keys(J`ReductionObj) then
		return J`ReductionObj[p];
	end if;
	require IsPrime(p) : "p must be a prime";
	require BaseRing(J`C) eq Rationals() : "Jacobian must be defined over the rationals";
	Cp := ChangeRing(J`C, GF(p));
	Rp := CoordinateRing(Ambient(Cp));
	I_num := Ideal(Numerator(J`D_def));
	I_den := Ideal(Denominator(J`D_def));
	I_num_p := ideal< Rp | Generators(Reduction(I_num, p)) >;
	I_den_p := ideal< Rp | Generators(Reduction(I_den, p)) >;
	D := Divisor(Cp, I_num_p) - Divisor(Cp, I_den_p);
	Jp := GenericJacobian(Cp, D);
	phi := hom<Rationals()->GF(p)|>;
	rho := hom<CoordinateRing(Ambient(J`C))->Rp | phi, [Rp.i : i in [1..Rank(Rp)]] >;
	J`ReductionObj[p] := Jp;
	J`ReductionDivMap[p] := rho;
	return Jp;
end intrinsic;

intrinsic BaseChange(Pt::JacCrvPt, Jphi::JacCrv, rho::Map)->JacCrvPt
{Base change of point on Jacobian}
	ID := Ideal(Pt);
	Iphi := ideal<Codomain(rho)|[rho(x) : x in NormalisedGenerators(ID)]>;
	Dphi := Divisor(Jphi`C, Iphi);
	Pphi := Point(Jphi, Dphi);
	Pphi`Ideal := Iphi;
	//assert(Degree(Pt`D) eq Degree(Dphi)); Be careful to not use this function for non-morphisms, i.e. Q->F_p.
	return Pphi;
end intrinsic;

intrinsic Reduction(Pt::JacCrvPt, p::RngIntElt)->JacCrvPt
{Reduction of point on Jacobian}
	Jp := Reduction(Pt`J, p);
	return BaseChange(Pt, Jp, Pt`J`ReductionDivMap[p]);
end intrinsic;

intrinsic PointOverSmallestField(J::JacCrv, Pt::JacCrvPt)->JacCrvPt
{For a Jacobian over Q and a point over a number field, try to put the point in the Jacobian over a smaller number field, if possible.}
	require BaseRing(J`C) eq Rationals() : "Jacobian must be defined over the rationals";
	//print "PointsOverSmallestField", Decomposition(Pt`D);
	L := BaseField(Pt`J`C);
	if IsPrimeField(L) then
		return Pt;
	end if;
	I := Ideal(Pt);
	GB := GroebnerBasis(I);
	K := sub<L | &cat[ Coefficients(x) : x in GB ]>;
	if K eq L then
		if IsFinite(K) then
			if not(#K in Keys(J`ReductionObj)) then
				b, p := IsPrimePower(#K);
				J`ReductionObj[#K] := BaseChange(Reduction(J,p), hom<GF(p)->K|>);
			end if;
			Jq := J`ReductionObj[#K];
			if not(Pt`J eq Jq) then
				M := BaseField(Jq`C);
				phi := hom<K->M | Roots(MinimalPolynomial(K.1), M)[1][1]>;
				RK := CoordinateRing(Ambient(Pt`J`C));
				RL := CoordinateRing(Ambient(Jq`C));
				rho := hom<RK->RL | [RL.i : i in [1..Rank(RK)]]>;
				return BaseChange(Pt, Jq, rho);
			end if; 
		end if;
		return Pt;
	elif IsFinite(K) then
		b, p := IsPrimePower(#K);
		if not(#K in Keys(J`ReductionObj)) then
			J`ReductionObj[#K] := BaseChange(Reduction(J,p), hom<GF(p)->K|>);
		end if;
		Jq := J`ReductionObj[#K];
		Fq := BaseField(Jq`C);
		if IsPrimeField(Fq) then
			psi := hom<K->Fq | >;
		else
			psi := hom<K->Fq | Fq.1>;
		end if;
		RK := ChangeRing(CoordinateRing(Ambient(Pt`J`C)), K);
		Rp := CoordinateRing(Ambient(Jq`C));
		phi := hom< RK->Rp | psi, [Rp.i : i in [1..Rank(Rp)]] >; 
		I_Rp := ideal< Rp | [phi(RK!x) : x in GB] >;
		Dq := Divisor(Jq`C, I_Rp);
		Pt_sm := Point(Jq, Dq);
		Pt_sm`Ideal := I_Rp;
		return Point(Jq, Dq);
	elif K eq Rationals() then
		RK := CoordinateRing(Ambient(J`C));
		I_K := ideal< RK | [RK!x : x in GB] >;
		DK := Divisor(J`C, I_K);
		PK := Point(J, DK);
		PK`Ideal := I_K;
		return PK;
	else
		//JK := BaseChange(J, hom<Rationals()->K|>);
		K_opt, phi := Polredabs(K : Best := true);
		JK_opt := BaseChange(J, hom<Rationals()->K_opt|>);
		RK_opt := CoordinateRing(Ambient(JK_opt`C));
		RK := ChangeRing(  CoordinateRing(Ambient(Pt`J`C)) ,K);
		rho := hom< RK->RK_opt | phi, [RK_opt.i : i in [1..Rank(RK)]]>;
		I_K_opt := ideal< RK_opt | [rho(RK!x) : x in GB] >;
		DK_opt := Divisor(JK_opt`C, I_K_opt);
		PK_opt := Point(JK_opt, DK_opt);
		PK_opt`Ideal := I_K_opt;
		return PK_opt;
	end if;
end intrinsic;

intrinsic PrimeReduction(J::JacCrv, Pt::JacCrvPt, p::RngIntElt : OnlyLinear := false)->SetEnum
{Input: a Jacobian J over Q, a point Pt over the base change of J to a number field, and a prime p.
Output: all possible reductions to finite fields of characteristic p of the point Pt.}
	require IsPrime(p) : "p must be a prime";
	require BaseRing(J`C) eq Rationals() : "Jacobian must be defined over the rationals";
	K := BaseField(Pt`J`C);
	GenDenominator := LCM([Denominator(c) : c in Coefficients(DefiningPolynomial(K))]);
	require GenDenominator eq 1: "Defining polynomial for number field must be integral.";
	if K ne Rationals() then
		require Valuation(Discriminant(EquationOrder(K)), p) eq 0: "Defining polynomial for number field cannot have factor p in its discriminant.";
	end if;
	OK := RingOfIntegers(K);
	S := {};
	for pI in Factorisation(ideal< OK | p >) do
		q := Norm(pI[1]);
		if OnlyLinear and (q gt p) then
			continue pI;
		end if;
		if not(q in Keys(J`ReductionObj)) then
			J`ReductionObj[q] := BaseChange(Reduction(J, p), hom<GF(p)->GF(q)|>);
		end if;
		Jq := J`ReductionObj[q];
		Fq := BaseField(Jq`C);
		k, phi := ResidueClassField(pI[1]);
		if p eq q then
			psi := hom<k->Fq | >;
		else
			psi := hom<k->Fq | Roots(ChangeRing(MinimalPolynomial(k.1), Fq))[1][1] >;
		end if;
		if AbsoluteDegree(K) ne 1 then
			theta := hom<OK->Fq | [psi(phi(x)) : x in Basis(OK) ] >;
		else
			theta := hom<OK->Fq | >;
		end if;
		RL := CoordinateRing(Ambient(Pt`J`C));
		ROK := PolynomialRing(OK, Rank(RL));
		Rp := CoordinateRing(Ambient(Jq`C));
		rho := hom< ROK->Rp | theta, [Rp.i : i in [1..Rank(Rp)]] >;
		I_Pt := Ideal(Pt);
		if AbsoluteDegree(K) eq 1 then
			Pt_Iq := Reduction(I_Pt, p);
		else
			Pt_Iq := AlternativeReduction(I_Pt, Place(pI[1]));
		end if;
		rho := hom< Pt_Iq^0->Rp | psi, [Rp.i : i in [1..Rank(Rp)]]>;
		Pt_Iq := ideal<Rp | [rho(x) : x in Generators(Pt_Iq)]>;
		D_q := Divisor(Jq`C, Pt_Iq);
		//assert(Degree(D_Pt) eq Degree(D_q));
		Pt_q := Point(Jq, D_q);
		if not(IsPrimeField(Fq)) then
			Pt_q := PointOverSmallestField(J, Pt_q);
		end if;
		Fq := BaseField(Pt_q`J`C);
		Pt_q_Frob := Pt_q;
		Frob_Fq := FrobeniusMap(Fq);
		NrOfFrobenii := 1;
		repeat
			Include(~S, Pt_q_Frob);
			if Degree(Fq) eq NrOfFrobenii then
				continue pI;
			end if;
			NrOfFrobenii +:= 1;
			Pt_q_Frob := ApplyAutomorphism(Pt_q_Frob, Frob_Fq);
		until Pt_q_Frob eq Pt_q;
	end for;
	return S;
end intrinsic;

intrinsic Order(J::JacCrv)->RngIntElt
{Order of Jacobian}
	if J`Order gt 0 then
		return J`Order;
	end if;
	require IsFinite(BaseRing(J`C)) : "Jacobian must be defined over finite field";
	J`Order := Evaluate(LPolynomial(J`C), 1);
	return J`Order;
end intrinsic;

intrinsic Order(Pt::JacCrvPt)->RngIntElt
{Order of point on Jacobian}
	if Pt`Order ne 0 then
		OrderFound := false;
		while OrderFound eq false do
			OrderFound := true;
			for p in PrimeDivisors(Pt`Order) do
				if Integers()!(Pt`Order / p) *Pt eq 0 then
					OrderFound := false;
				end if;
			end for;
		end while;
		return Pt`Order;
	end if;
	if Pt`J`Order gt 0 then
		for d in Divisors(Pt`J`Order) do
			if d*Pt eq 0 then
				return d;
			end if;
		end for;
	else
		n := 1;
		nPt := Pt;
		while not(nPt eq 0) do
			nPt +:= Pt;
			n +:= 1;
		end while;
		Pt`Order := n;
		return n;
	end if;
end intrinsic;

function RandomDivisor(J, A, d)
	Monoms := MonomialsOfDegree(A, d);
	f := &+[Random(BaseRing(A))*x : x in Monoms];
	I := ideal<Parent(f) | f >;
	return Divisor(Random(Decomposition(Divisor(J`C, I)))[1]);
end function;

intrinsic Random(J::JacCrv)->JacCrvPt
{Random point on Jacobian}
	require IsFinite(BaseRing(J`C)) : "Jacobian must be defined over finite field";
	A := CoordinateRing(Ambient(J`C));
	d := Degree(J`D_can); d := d + Ceiling(Genus(J`C)/d)*d;
	RandD := RandomDivisor(J, A, d);
	while (Degree(RandD) lt d) or (Degree(RandD) mod Degree(J`D_can) ne 0) do
		RandD +:= RandomDivisor(J, A, d);
	end while;	
	return InternalPoint(J, RandD);
end intrinsic;

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

intrinsic JacobianSubgroup(J::JacCrv, L::SeqEnum[JacCrvPt])->SetEnum
{Create subgroup in Jacobian}
	Subgroup := {Zero(J)};
	for x in L do
		AddElementToSubgroup(~Subgroup, x);
	end for;
	return Subgroup;
end intrinsic;

intrinsic pSylowSubgroup(J::JacCrv, p::RngIntElt)->SetEnum
{Compute p-Sylow subgroup in J}
	require IsPrime(p) : "p has to be prime";
	if not(p in Keys(J`pSylowSubgroup)) then
		print "Computing Sylow-", p , "group";
		print "over base field", BaseField(J`C);
		Subgroup := {Zero(J)};
		pOrder := p^Valuation(Order(J), p);
		print "pOrder =", pOrder;
		cOrder := Integers()! (Order(J) / pOrder);
		print "cOrder =", cOrder;
		while #Subgroup lt pOrder do
			RandPt := Random(J);
			AddElementToSubgroup(~Subgroup, cOrder*RandPt);
		end while;
		J`pSylowSubgroup[p] := Subgroup;
	end if;
	return J`pSylowSubgroup[p];
end intrinsic;

intrinsic AlternativeReduction(I::RngMPol, p::Any : parent := false) -> RngMPol
  { Given an ideal I in a graded polynomial ring over a number field and
  p, a place or a prime ideal of an order in that number field, compute the
  reduction of I mod p - that is, the defining ideal of the flat
  completion of the corresponding projective scheme. }

  RK := Generic(I);
  K := BaseRing(RK);
  if Type(K) eq FldRat then
    RZ := ChangeRing(RK,Integers());
    if ISA(Type(parent), RngMPol) then
      require BaseRing(parent) eq GF(p) : "parent should be a polynomial ring over GF(p)";
      R := parent;
    else
      require parent cmpeq false : "parent should be a polynomial ring";
      R := ChangeRing(RK,GF(p));
    end if;
    gens := [ RZ | ];
    // Clear denominators
    for f in Generators(I) do
      d := LCM([Denominator(c) : c in Coefficients(f)]);
      Append(~gens, f*d);
    end for;
    // Make it flat at p by removing any extra components lying over p
    J := ideal< RZ | gens >;
    J := ColonIdeal(J, RZ!p); // actually does saturation, not colon ideal
    return ideal<R | Basis(J)>;
  else
    require ISA(Type(K), FldNum) : "Ideal must be over a number field";
    // Find the Hilbert polynomial of the ideal
    P := HilbertPolynomial(I);
    
    // Form the ambient ring over the residue field
    require (Type(p) cmpeq RngOrdIdl) or (Type(p) cmpeq PlcNumElt):
	"p should be a number field place or the prime ideal of an order";
    pi := UniformizingElement(p);
    if Type(p) cmpeq RngOrdIdl then
      F,m := ResidueClassField(p);
    else
      p := Ideal(p); //replace p by corr RngOrdIdl
      F,m := ResidueClassField(p);
      //m := func<x|Evaluate(x,p)>; // the reduction mod p map
    end if;
    if ISA(Type(parent), RngMPol) then
      require BaseRing(parent) eq F : "Parameter `parent' should be a ring over the residue field";
      R := parent;
    else
      R := ChangeRing(RK,F);
    end if;
    
    // Now clear denominators
    gens := [ f/pi^v where v := Min([Valuation(c,p) : c in Coefficients(f)])
    		: f in Basis(I) ];
    
    // Try reducing mod p, and see what we get
    pgens := [ R | ];
    for g in gens do
      C,M := CoefficientsAndMonomials(g);
      Append(~pgens, Polynomial( [m(c) : c in C], [R!x : x in M] ));
    end for;
    Ip := ideal<R | pgens>;
    // If it has the correct Hilbert polynomial, then our model is flat
    if HilbertPolynomial(Ip) eq P then
      return Ip;
    end if;
    
    // Otherwise, we need to do some saturation.  We can't do this
    // over the number ring, but we can do it over a p-adic residue
    // ring of sufficient precision.
    O := Order(p);
    Op,mp := Completion(O,p);
    pi := UniformizingElement(Op);
    
    // Find a starting precision - maximum valuation of the coefficients,
    // or 10, whichever is greater.
    prec := Max([ Max([ Valuation(c,p) : c in Coefficients(f)]) : f in gens ] cat [10] );
    // Maybe we should try for ever...
    for tries in [1..10] do
      // Form the quotient ring and base change everything
      S := quo< Op | pi^prec >;
      RS := ChangeRing(RK,S);
      Sgens := [RS | ];
      for f in gens do
	C,M := CoefficientsAndMonomials(f);
	// 12/18 - mch - elements of C are p-integral but not nec in O -
	// must scale by (prime to p) denominators
	den := LCM([Denominator(c) : c in C]);
	C := [c*den : c in C];
	
	Append(~Sgens, Polynomial( [S!mp(O!c) : c in C], [RS!x : x in M] ));
      end for;
      IS := ideal<RS|Sgens>;
      F,q := ResidueClassField(S);
      // 12/18-mch - if F is a non-prime-field, must explicitly find
      // the embedding from BaseRing(R) to F - no automatic coercion!
      // Do in a try clause as this throws an error if the fields are
      // already linked internally.
      try Embed(BaseRing(R),F,q(S!(mp((BaseRing(R).1)@@m)))); catch e; end try;
      // Take colon ideals until we get a flat model, or we run out
      // of precision
      for i in [1..prec] do
	IS := ColonIdeal(IS, ideal<RS|pi>);
	Fgens := [];
	for f in Basis(IS) do
	  C,M := CoefficientsAndMonomials(f);
	  Append(~Fgens, Polynomial( [BaseRing(R)!q(c) : c in C],
			[Monomial(R,Exponents(x)) : x in M] ));
	end for;
	Ip := ideal<R | Fgens >;
	if HilbertPolynomial(Ip) eq P then
	  return Ip;
	end if;
      end for;
      // No luck - increase the precision
      prec +:= 10;
    end for;
    error "Couldn't find flat completion up to precision", prec-10;
  end if;
end intrinsic;
