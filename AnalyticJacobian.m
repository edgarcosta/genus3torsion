function NumericalJacobian(f)
	// Given a function f, produce a function that numerically computes the Jacobian of f.
	// Precision is lost by a factor 1/2, which should not matter so much for Newton-Raphson.
	df := function(x : fx := [])
		prec := Precision(x[1][1]);
		d := 10^Floor(-prec/2);
		n := NumberOfRows(x);
		M := [];
		if Type(fx) eq SeqEnum then
			fx := f(x);
		end if;
		for i in [1..n] do
			xi := x;
			xi[i][1] +:= d;
			fxi := f(xi);
			Append(~M, (fxi-fx)/d);
		end for;
		return Transpose(Matrix(M));
	end function;
	return df;
end function;

function NewtonRaphson(f, x0 : df := [], fx0 := [], prec := 0, Verbose := false)
	// This implements Newton-Raphson for a function C^n -> C^n.
	// This even works when the derivative is not available; numerical differentiation will be used.
	n := 0;
	if prec eq 0 then
		prec := Precision(x0[1][1]);
	end if;
	xn := x0;
	dif := 1.0;
	if Type(df) eq SeqEnum then
		df := NumericalJacobian(f);
	end if;
	while dif gt RealField(prec)!10^(2-prec) and n lt 100 do
		n +:= 1;
		xprev := xn;
		if n eq 1 and Type(fx0) ne SeqEnum then
			fxn := fx0;
		else
			fxn := f(xn);
		end if;
		dxn := df(xn : fx := fxn);
		assert Abs(Determinant(dxn)) gt 10^-Floor(prec/10);
		xn := xn - dxn^(-1)*fxn;
		dif := Abs(Determinant(dxn))*&+[ Real(Norm(xn[i][1] - xprev[i][1])) / Max(1, Abs(xn[i][1])) : i in [1..NumberOfRows(xn)]]^(0.5);
		if n gt 5 then
			assert(dif lt 1);
		end if;
		if Verbose then
			print "Newton-Raphson step", n, ": ", dif;
		end if;
		//print xn - Qx;
	end while;
	return xn;
end function;


function RandomComplexPoint(C, F)
	prec := Precision(F);
	x := Random(10^prec) / F!10^(prec-2) + F.1 * Random(10^prec) / F!10^(prec-2);
	_<X> := PolynomialRing(F);
	f := Evaluate(Equation(C), [x, X, 1]);
	y := Random(Roots(f))[1];
	return [x,y];
end function;

function CloseComplexPoint(C, x, y : Chart := 1, Swap := false)
	// Of all points with given x-coordinate, find the one whose y-coordinate is closest to given y-coordinate.
	// If parameter Swap is set, then do the opposite: find a close point with given y-coordinate.
	_<X> := PolynomialRing(Parent(x));
		
	if not(Swap) then
		if Chart eq 1 then
			eqn := Evaluate(Equation(C), [x, X, 1]);
		elif Chart eq 2 then
			eqn := Evaluate(Equation(C), [X, 1, x]);
		else
			eqn := Evaluate(Equation(C), [1, x, X]);
		end if;
		d_eqn := Derivative(eqn);
		
		func := function(s)
			return Matrix([[Evaluate(eqn, s[1][1])]]);
		end function;
		dfunc := function(s : fx := 0)
			return Matrix([[Evaluate(d_eqn, s[1][1])]]);
		end function;
		try
			y_corr := NewtonRaphson(func, Matrix([[y]]) : df := dfunc);
			return [x, y_corr[1][1]];
		catch e
			// If there happens to be ramification, try the slow method.
			z := Roots(eqn);
			min_dist, i := Min( [Abs(w[1] - y) : w in z] );
			return [x, z[i][1]];
		end try;
	else
		if Chart eq 1 then
			eqn := Evaluate(Equation(C), [X, y, 1]);
		elif Chart eq 2 then
			eqn := Evaluate(Equation(C), [y, 1, X]);
		else
			eqn := Evaluate(Equation(C), [1, X, y]);
		end if;
		d_eqn := Derivative(eqn);
		
		func := function(s)
			return Matrix([[Evaluate(eqn, s[1][1])]]);
		end function;
		dfunc := function(s : fx := 0)
			return Matrix([[Evaluate(d_eqn, s[1][1])]]);
		end function;
		try
			x_corr := NewtonRaphson(func, Matrix([[x]]) : df := dfunc);
			return [x_corr[1][1], y];
		catch e
			// If there happens to be ramification, try the slow method.
			z := Roots(eqn);
			min_dist, i := Min( [Abs(w[1] - x) : w in z] );
			return [z[i][1], y];
		end try;	
	end if;
	//R := Roots(f);
	//d, i := Min( [ Abs(r[1]-y) : r in R ]);
	//return [x, R[i][1]];
end function;


procedure Add(~M, i, x)
	// Add value to entry in associative array.
	// If the entry does not exist, create it.Numera
	if not(i in Keys(M)) then
		M[i] := x;
	else
		M[i] +:= x;
	end if;
end procedure;


function NumericalDerivative(C, f, x, order, degree : Chart := 1)
	//print "Start numerical derivative", order;
	prec := Precision(x[1]);
	reqprec := (order+2)*prec;
	d := 10^Floor(1-prec);
	coeffs := [AssociativeArray(), AssociativeArray()];
	coeffs[1][0] := 1;
	coeffs[2][-1] := -1/2;
	coeffs[2][1] := 1/2;
	for i in [1..order+1] do
		// Generate coefficients if necessary
		if i gt 2 then
			Append(~coeffs, AssociativeArray());
			for j in Keys(coeffs[i-2]) do
				Add(~coeffs[i], j-1,  coeffs[i-2][j]);
				Add(~coeffs[i], j, -2*coeffs[i-2][j]);
				Add(~coeffs[i], j+1,  coeffs[i-2][j]);
			end for;
		end if;
		if i eq order+1 then
			// Check for vanishing of order i
			x_i := [ComplexField(reqprec)!c : c in x];
			df_val := ComplexField(reqprec)!0;
			R<a,b,c> := PolynomialRing(ComplexField(reqprec), 3);
			f_hom := Homogenization( Evaluate(  ChangeRing(f, ComplexField(reqprec)), [a,b]) + c^degree, c ) - c^degree;
			if Chart eq 1 then
				if Abs(Evaluate(Derivative(Equation(C), Parent(Equation(C)).2), [x[1], x[2], 1])) lt Abs(Evaluate(Derivative(Equation(C), Parent(Equation(C)).1), [x[1], x[2], 1])) then
					Swap := true;
				else
					Swap := false;
				end if;
				f_func := function(s, j)
					Pt := CloseComplexPoint(C, s[1] + j*d, s[2] + j*d : Chart := Chart, Swap := Swap);
					return Evaluate(f_hom, [Pt[1], Pt[2], 1]);
				end function;
			elif Chart eq 2 then
				if Abs(Evaluate(Derivative(Equation(C), Parent(Equation(C)).1), [x[2], 1, x[1]])) lt Abs(Evaluate(Derivative(Equation(C), Parent(Equation(C)).3), [x[2], 1, x[1]])) then
					Swap := true;
				else
					Swap := false;
				end if;
				f_func := function(s, j)
					Pt := CloseComplexPoint(C, s[1] + j*d, s[2] + j*d : Chart := Chart, Swap := Swap);
					return Evaluate(f_hom, [Pt[2], 1, Pt[1]]); // This is not actually the right function, but for our purpose that does not matter.
				end function;
			elif Chart eq 3 then
				if Abs(Evaluate(Derivative(Equation(C), Parent(Equation(C)).3), [1, x[1], x[2]])) lt Abs(Evaluate(Derivative(Equation(C), Parent(Equation(C)).2), [1, x[1], x[2]])) then
					Swap := true;
				else
					Swap := false;
				end if;
				f_func := function(s, j)
					Pt := CloseComplexPoint(C, s[1] + j*d, s[2] + j*d : Chart := Chart, Swap := Swap);
					return Evaluate(f_hom, [1, Pt[1], Pt[2]]); // See also comment above.
				end function;
			else
				assert(false);
			end if;
			for j in Keys(coeffs[i]) do
				df_val +:= coeffs[i][j]*f_func(x_i, j);
			end for;
			df_val /:= d^(i-1);
			//print i, [coeffs[i][j] : j in Keys(coeffs[i])], df_val;
			//print "End numerical derivative";
			//assert(Chart eq 1 or Exponents(Monomials(f)[1]) ne [1, 0]);
			return ComplexField(prec)!df_val;
		end if;
	end for;
end function;

function NumericalGCD(f,g : eps := 10^-5)
	if Degree(g) gt Degree(f) then
		return NumericalGCD(g,f : eps := eps);
	elif (Degree(g) eq Degree(f)) and (Abs(LeadingCoefficient(g)) lt Abs(LeadingCoefficient(f))) then
		return NumericalGCD(g,f : eps := eps);
	end if;
	if (g eq 0) or (Max([Abs(x) : x in Coefficients(g)]) lt eps) then
		return f;
	else
		if Abs(LeadingCoefficient(g)) lt eps^2 then
			return NumericalGCD(f, g-LeadingTerm(g) : eps := eps);
		end if;
		return NumericalGCD(g, f mod g : eps := eps);
	end if;
end function;


function InternalNumericalResultant(f, g : eps := 10^-6)
	print f, g;
	if (g eq 0) then
		return f;
	elif Max([Abs(x) : x in Coefficients(LeadingCoefficient(g))]) lt eps then
		return InternalNumericalResultant(f, g - LeadingTerm(g));
	else
		f_mod_g := f;
		new_g := g;
		while Degree(f_mod_g) ge Degree(g) do
			new_f_mod_g := LeadingCoefficient(new_g) * f_mod_g - LeadingCoefficient(f_mod_g) * new_g * Parent(g).1^(Degree(f_mod_g) - Degree(g));
			new_g := LeadingCoefficient(f_mod_g) * new_g;
			f_mod_g := new_f_mod_g;
		end while;
		return InternalNumericalResultant(new_g, f_mod_g);
	end if;
end function;

function NumericalResultant(f, g, i : eps := 10^-6)
	A := Parent(f);
	R := BaseRing(A);
	B<x> := PolynomialRing(R);
	C<y> := PolynomialRing(B);
	if i eq 1 then
		fC := Evaluate(f, [x, y]);
		gC := Evaluate(g, [x, y]);
		h := InternalNumericalResultant(fC, gC : eps := eps);
	else
		fC := Evaluate(f, [y, x]);
		gC := Evaluate(g, [y, x]);
		h := InternalNumericalResultant(fC, gC : eps := eps);
	end if;
	return h;
end function;

function NumericalZeros(C, f : Ignore := [], AllowInfinity := true, IgnoreInf := [], RaiseError := false)
	//print "Start numerical zeros";
	CC := ComplexField(2*Precision(BaseRing(Parent(f))));
	eps := 10^-Floor(Precision(CC)/8);
	R<xC, yC> := PolynomialRing(CC, 2);
	eqn := Evaluate(Equation(C), [xC,yC,1]);
	//Write("pol1", eqn);
	fC := Evaluate(f, [xC, yC]);
	mon_fC := Monomials(fC);
	coef_fC := Coefficients(fC);
	for i in [1..#mon_fC] do
		if Abs(coef_fC[i]) lt Sqrt(eps) then
			fC -:= coef_fC[i] * mon_fC[i];
		end if;
	end for;
		
	//Write("pol2", fC);
	func := function(x)
		return Matrix([[Evaluate(f, [x[1][1], x[2][1]])], [Evaluate(Equation(C), [x[1][1], x[2][1], 1])]]);
	end function;
		
	GB := [eqn, fC, Resultant(fC, eqn, xC)];
	
	Zeros := {};
	S<z> := PolynomialRing(CC);
	prev_y := {};
	res_poly := Evaluate(GB[#GB], [0, z]);
	while Abs(LeadingCoefficient(res_poly)) lt eps do
		res_poly -:= LeadingTerm(res_poly);
	end while;
	if AllowInfinity then
		if Degree(res_poly) lt Degree(f)*Degree(eqn) then
			A<xA> := PolynomialRing(CC);
			fx := Evaluate(Equation(C), [xA, 1, 0]);
			fy := Evaluate(Equation(C), [1, xA, 0]);
			PotentialInfPoints := [[x[1], 1] : x in Roots(fx) ];
			if Abs(Evaluate(fy, 0)) lt eps then
				Append(~PotentialInfPoints, [CC!1, CC!0]);
			end if;
			for Pt in PotentialInfPoints do
				fPt := Evaluate(f, [Pt[1]*xA, Pt[2]*xA]);
				if (Abs(LeadingCoefficient(fPt)) lt eps) or (Degree(fPt) lt Degree(f)) then
					IsPointExcluded := false;
					for y in IgnoreInf do
						if Abs(y[1]*Pt[2] - y[2]*Pt[1]) lt eps then
							IsPointExcluded := true;
						end if;
					end for;
					if IsPointExcluded eq false then
						Include(~Zeros, Pt cat [0]);
					end if;
				end if;
			end for;
		elif Degree(res_poly) gt Degree(f)*Degree(eqn) then
			assert(false);
		end if;
	else
		assert(Degree(res_poly) le Degree(f)*Degree(eqn));
	end if;
	rts_resultants := Roots(res_poly);
	for i in [#rts_resultants..1 by -1] do
		for y in Ignore do
			if Abs(rts_resultants[i][1]-y) lt Sqrt(eps) then
				Remove(~rts_resultants, i);
				continue i;
			end if;
		end for;
	end for;

	for y in [r[1] : r in rts_resultants] do
		for y2 in prev_y do
			if Abs(y - y2) lt eps then
				continue y;
			end if;
		end for;
		Include(~prev_y, y);
		pols := [Evaluate(GB[i], [z, y]) : i in [1..#GB-1]];
		p := NumericalGCD(pols[1], pols[2] : eps := 1E-20);
		//print Degree(p);
		//print(p);
		assert(Abs(LeadingCoefficient(p)) gt eps);
		prev_x := {};
		for x in [r[1] : r in Roots(p)] do
			for x2 in prev_x do
				if Abs(x - x2) lt eps then
					continue x;
				end if;
			end for;
			Include(~prev_x, x);
			if (Abs(Evaluate(Equation(C), [x, y, 1])) gt eps) or (Abs(Evaluate(f, [x, y])) gt eps) then
				continue x;
			end if;
			//Include(~Zeros, [Pt[1][1], Pt[2][1]]);
			Include(~Zeros, [x,y]);
		end for;
	end for;
	
	// Check for zeros when fC has factors only depending on x.
	R1<zC> := PolynomialRing(CC);
	random_y := (-1)^Random(2) * CC!Random(10^Precision(CC)) / 10^Precision(CC) + (-1)^Random(2) * CC!Random(10^Precision(CC)) / 10^Precision(CC) * CC.1;
	f1 := Evaluate(fC, [zC, random_y]);
	for r in Roots(f1) do
		x := r[1];
		y_pol := Evaluate(eqn, [x, zC]);
		for s in Roots(y_pol) do
			y := s[1];
			if Abs(Evaluate(fC, [x,y])) lt eps then
				PointNotListed := true;
				for p in Zeros do
					if (Abs(x - p[1]) lt Sqrt(eps)) and (Abs(y - p[2]) lt Sqrt(eps)) then
						PointNotListed := false;
					end if;
				end for;
				if PointNotListed then
					Include(~Zeros, [x,y]);
				end if;				
			end if;
		end for;
	end for;
	
	assert(RaiseError eq false);
	return Zeros;
end function;

function NumericalRiemannRoch(C, D, BasePt : Precision := 200)
	CC := ComplexField(Precision);
	Dplus := [ i : i in D | i[2] gt 0];
	Dmin := [ [i[1], -i[2]] : i in D | i[2] lt 0];
	BaseDiv := Divisor(BasePt);
	deg_plus := &+[ i[2] : i in D ];
	R := PolynomialRing(CC, 2);
	
	// Step 1: find a function f such that f vanishes at Dplus, this can be found in O(n*BasePt - Dplus) for n big enough.
	RR1 := [Evaluate(Numerator(x), [R.1, R.2]) / Evaluate(Denominator(x), [R.1, R.2]) : x in Basis( (deg_plus+Genus(C))*BaseDiv )];
	NumDerivs := [
					 &cat[ [ NumericalDerivative(C, g, d[1][1], j : Chart := d[1][2])   : j in [0..d[2]-1] ] : d in D]
				: g in RR1 ];
	K := Basis(Kernel(Matrix(NumDerivs)));
	c := [ CC!1 + Random(10^9)/10^9 : i in [1..#K] ];
	v := &+[c[i]*K[i] : i in [1..#K]];
	f := &+[ v[i]*RR1[i] : i in [1..#RR1]];
	
	Zf := NumericalZeros(C, f);
	/*for z in Zf do
		print z;
	end for;*/
	assert(false);
end function;

function LineIntersections(C, f, a, b, c : eps := 10^(-6))
// Intersection of f with line ax + by + c = 0
	F := BaseRing(Parent(f));
	R<x> := PolynomialRing(F);
	fR := Evaluate(f, [x, -(a*x + c) / b, 1]);
	assert(Abs(Discriminant(fR)) gt eps);
	return [CloseComplexPoint(C, x[1], -(a*x[1] + c)/ b) : x in Roots(fR)];	
end function;

function RandomLine(C, RS)
	F := ComplexField(Precision(RS));
	a := (-1)^Random(2) * F!Random(10^Precision(RS)) / 10^Precision(RS);
	b := (-1)^Random(2) * F!Random(10^Precision(RS)) / 10^Precision(RS);
	c := (-1)^Random(2) * F!Random(10^Precision(RS)) / 10^Precision(RS);
	return [RS!x : x in LineIntersections(C, Equation(C), a, b, c : eps := 10^-Floor(Precision(RS)/10))];	
end function;

function ToAnalyticJacobianFunction(C, RS : Q := [], Rs := [], Goal := 0)
	F := Parent(Coordinates(BasePoint(RS))[1]);
	if #Q eq 0 then
		Rs := [RandomComplexPoint(C, F) : i in [1..Genus(C)]];
		Q := [RS!x : x in Rs];
	end if;

	f := function(s)
		P := [RS!CloseComplexPoint(C, s[i][1], Rs[i][2]) : i in [1..Genus(C)]];
		if Goal ne 0 then
			return Transpose( Matrix([  &+[AbelJacobi(Q[i], P[i]) : i in [1..Genus(C)]] ]) ) - Goal;
		else
			return Transpose( Matrix([  &+[AbelJacobi(Q[i], P[i]) : i in [1..Genus(C)]] ]) );
		end if;
	end function;
	return f, Q;
end function;

function JacobianDerivativeFunction(C, RS, Q : Rs := [])
	if #Rs eq 0 then
		Rs := Q;
	end if;
	D := HolomorphicDifferentials(RS);
	M := [];
	R<x,y> := PolynomialRing(Rationals(), 2);
	f := Evaluate(Equation(C), [x,y,1]);
	N := Transpose(Matrix(Transpose(BigPeriodMatrix(RS))[[1..Genus(C)]]))^(-1);
	for d in D[1] do
		g := x^(d[1]-1) * y^(d[2]-1) / Evaluate(D[2], [x,y]);
		Append(~M, g);
	end for;
	//print M;
	f := function(s : fx := 0)
		P := [CloseComplexPoint(C, s[i][1], Rs[i][2]) : i in [1..Genus(C)]];
		return N*Matrix( [ [ Evaluate(m,P[i]) : i in [1..Genus(C)] ] : m in M] );
	end function;
	return f;
end function;

function ZeroModPeriods(M, x)
	CC := Parent(M[1][1]);
	ReducedMatrix := Transpose(Matrix(Transpose(M)[1..3]))^(-1)*M;
	FullMatrix := Matrix([  &cat[ [Real(ReducedMatrix[j][i]), Imaginary(ReducedMatrix[j][i])] : j in [1..3] ]  : i in [1..6]]);
	xFull := Matrix([  &cat[ [Real(x[j][i]), Imaginary(x[j][i])] : j in [1..3] ]  : i in [1]]);
	y := Transpose(FullMatrix)^(-1)*Transpose(xFull);
	err := Max( [ Abs(y[i][1] - Round(y[i][1])) : i in [1..6] ]);
	y_round := Matrix([ [CC!Round(y[i][1])] : i in [1..6]]);
	return err, ReducedMatrix*y_round;
end function;

function EqualModPeriods(M, x, y)
	return ZeroModPeriods(M, x-y);
end function;

function MyKernel(M : eps := 10^(-6))
	n := NumberOfRows(M);
	assert(n eq NumberOfColumns(M)+1);
	Dets := [Abs(Determinant(Matrix(M[Remove([1..n], i)]))) : i in [1..n]];
	MaxDet, i := Max(Dets);
	assert(MaxDet gt eps);
	N := M * Matrix(M[Remove([1..n], i)])^(-1);
	L := [N[i][j] : j in [1..n-1]];
	Insert(~L, i, -1);
	return L;
end function;

function AreDistinct(Pts)
	for i in [1..4] do
		for j in [i+1..4] do
			if Pts[i] eq Pts[j] then
				return false;
			end if;
		end for;
	end for;
	return true;
end function;

function Collinear(Pts : eps := 10^(-10))
	M := Matrix([Coordinates(Pt) : Pt in Pts]);
	if Abs(Determinant(M)) lt eps then
		return true;
	end if;
	return false;
end function;

function Interpolate(C, R, Pts, MaxDegree : eps := 10^(-6), BasePt := 0)
	//print "Start interpolate", Pts;
	// Find points with multiplicity
	PtsWithMultiplicity := [];
	for i in [1..#Pts] do
		Pt := Pts[i];
		if MaxDegree eq 2 then
			// Check for four points on a line, if so, replace Pt by BasePt
			for S in Subsets({1..i-1}, 3) do
				L := [j : j in S] cat [i];
				PtsL := Pts[L];
				if AreDistinct(PtsL) and Collinear(PtsL[[1..3]]) and Collinear(PtsL[[2..4]]) then
					assert(Type(BasePt) eq RieSrfPt);
					Pt := BasePt;
				end if;
			end for;
		end if;
		
		for j in [1..#PtsWithMultiplicity] do
			if PtsWithMultiplicity[j][1] eq Pt then
				PtsWithMultiplicity[j][2] +:= 1;
				continue i;
			end if;
		end for;
		CoordPt := Coordinates(Pt);
		if Abs(CoordPt[3]) gt eps then
			Append(~PtsWithMultiplicity, <Pt, 1, [1,2], 1>);
		elif Abs(CoordPt[2]) gt eps then
			Append(~PtsWithMultiplicity, <Pt, 1, [3,1], 2>);		
		elif Abs(CoordPt[1]) gt eps then
			Append(~PtsWithMultiplicity, <Pt, 1, [2,3], 3>);		
		else
			assert(false);
		end if;
	end for;
	// Interpolation step
	Monoms := &join[MonomialsOfDegree(R, i) : i in [0..MaxDegree]];
	M := Matrix([
			&cat[ [ NumericalDerivative(C, f, [Coordinates(Q[1])[k]/Coordinates(Q[1])[4-Q[4]] : k in Q[3]], j-1, MaxDegree : Chart := Q[4]) : j in [1..Q[2]] ]	: Q in PtsWithMultiplicity ]
			: f in Monoms ]);
	//print "Matrix complete";
	//print M;
	K := MyKernel(M : eps := 10^-Floor(Precision(M[1][1])/10));
	//K := Basis(Kernel(M));
	//assert(#K eq 1);
	//print "End interpolate";
	return &+[K[i]*Monoms[i] : i in [1..#Monoms]];
end function;

function ResidualIntersection(C, RS, R, Pts, f, ExpectedNumberOfPoints : PointsInRS := true, eps := 10^(-6), AllowInfinity := false, BasePt := 0)
	Zf := NumericalZeros(C,f : Ignore := [Coordinates(Pt)[2] : Pt in Pts | Abs(Coordinates(Pt)[3]) gt eps], AllowInfinity := AllowInfinity, IgnoreInf := [[Coordinates(Pt)[1], Coordinates(Pt)[2]] : Pt in Pts | Abs(Coordinates(Pt)[3]) lt eps]);
	//print "Start residual intersection";
	D := [];
	for Pt1 in Zf do
		if #Pt1 eq 3 then
			if PointsInRS then
				Append(~D, RS!Pt1);
			else
				Append(~D, Pt1);
			end if;
			continue Pt1;
		end if;
		for Pt2 in Pts do
			d := Abs(Pt1[1] - Coordinates(Pt2)[1]) + Abs(Pt1[2] - Coordinates(Pt2)[2]);
			if d lt Sqrt(eps) and Abs(Coordinates(Pt2)[3]) gt eps then
				continue Pt1;
			end if;
		end for;
		CPt1 := CloseComplexPoint(C, Pt1[1], Pt1[2]);
		d := Abs(CPt1[1] - Pt1[1]) + Abs(CPt1[2] - Pt1[2]);
		assert(d lt Sqrt(eps));
		if PointsInRS then
			Append(~D, RS!CPt1);
		else
			Append(~D, [CPt1[1], CPt1[2]]);
		end if;
	end for;
	if AllowInfinity and not(PointsInRS) and (#D lt ExpectedNumberOfPoints) then
		// Check for double vanishing (only implemented for the very last step)
		for j in [#D..1 by -1] do
			Pt := D[j];
			if (#Pt eq 2) or (Abs(Pt[3]) gt Sqrt(eps)) then
				Pt := Pt[[1,2]];
				Chart := 1;
			elif Abs(Pt[2]) gt Sqrt(eps) then
				Pt := [x/Pt[2] : x in Pt[[3,1]]];
				Chart := 2;
			elif Abs(Pt[1]) gt Sqrt(eps) then
				Pt := [x/Pt[1] : x in Pt[[2,3]]];
				Chart := 3;
			else
				assert(false);
			end if;
			for i in [1..ExpectedNumberOfPoints] do
				if Abs(NumericalDerivative(C, f, Pt, i, Degree(f) : Chart := Chart)) gt Sqrt(eps) then
					van_ord := i;
					break i;
				end if;
			end for;
			while van_ord gt 1 do
				Append(~D, D[j]);
				van_ord -:= 1;
			end while;
		end for;
	end if;
	if (#D lt ExpectedNumberOfPoints) and AllowInfinity and (Degree(f) eq 3) then
		// This happens only when we convert to another basis, in this case Pt[4] == Pt[5] == Pt[6] and we will check if is vanishing even more often.
		Pt := Coordinates(Pts[4]);
		if Abs(Pt[3]) gt Max(Abs(Pt[1]), Abs(Pt[2])) then
			PtChart := 1;
			Pt := Pt[[1,2]];
		elif Abs(Pt[2]) gt Abs(Pt[1]) then
			PtChart := 2;
			Pt := [Pt[i]/Pt[2] : i in [3,1]];
		else
			PtChart := 3;
			Pt := [Pt[i]/Pt[1] : i in [2,3]];
		end if;
		van_ord := 0;
		while Abs(NumericalDerivative(C, f, Pt, van_ord, Degree(f) : Chart := PtChart)) lt Sqrt(eps) do
			van_ord +:= 1;
			assert(van_ord le Degree(f)*Degree(Equation(C)));
		end while;
		assert(van_ord ge 3);
		while van_ord gt 3 do
			van_ord -:= 1;
			Append(~D, Pts[4]);
		end while;
	elif (#D lt ExpectedNumberOfPoints) and AllowInfinity and (Degree(f) eq 2) then
		// This happens in the basis conversion step when there is extra vanishing at the base point.
		Pt := Coordinates(BasePt);
		if Abs(Pt[3]) gt Max(Abs(Pt[1]), Abs(Pt[2])) then
			PtChart := 1;
			Pt := Pt[[1,2]];
		elif Abs(Pt[2]) gt Abs(Pt[1]) then
			PtChart := 2;
			Pt := [Pt[i]/Pt[2] : i in [3,1]];
		else
			PtChart := 3;
			Pt := [Pt[i]/Pt[1] : i in [2,3]];
		end if;
		van_ord := 0;
		while Abs(NumericalDerivative(C, f, Pt, van_ord, Degree(f) : Chart := PtChart)) lt Sqrt(eps) do
			van_ord +:= 1;
			assert(van_ord le Degree(f)*Degree(Equation(C)));
		end while;
		while van_ord gt #[Pt : Pt in Pts | Pt eq BasePt] do
			van_ord -:= 1;
			Append(~D, Coordinates(BasePt));
		end while;
		assert(#D eq ExpectedNumberOfPoints);	
	end if;
	assert(#D eq ExpectedNumberOfPoints);
	//print "End residual intersection";
	return D;
end function;


function FastAddition(C, RS, P, D1, D2 : AJ1 := [], Correction := true)
	// Implementation of modified Flon, Oyono, Ritzenthaler
	// Only works reliably when all intersections are transversal
	F := ComplexField(Precision(RS));
	eps := 10^-Floor(Precision(RS)/2);
	R<x,y> := PolynomialRing(F, 2);
	// Step -1: find a random point B
	B := [RS!RandomComplexPoint(C, F)];
	// Step 0a: find line through P1, P2
	c := Interpolate(C, R, P[[1,2]], 1);
	// Step 0b: find residual intersection A of line with C
	A := ResidualIntersection(C, RS, R, P[[1,2]], c, 2 : eps := eps);	
	// Step 1a: find a cubic through D1, D2, A, B
	c := Interpolate(C, R, D1 cat D2 cat A cat B, 3);
	// Step 1b: find residual intersection E of cubic with C
	E := ResidualIntersection(C, RS, R, D1 cat D2 cat A cat B, c, 3 : eps := eps);
	// Step 2a: find a conic through E, P3, B
	c := Interpolate(C, R, E cat P[[3]] cat B, 2);
	// Step 2b: find residual divisor D of conic with C
	// check order of vanishing of P3 on conic manually, because ResidualIntersection can't handle this case
	for i in [1..4] do
		if Abs(NumericalDerivative(C, c, Coordinates(P[3])[[1,2]], i, Degree(c))) gt eps then
			van_ord := i - 1;
			break i;
		end if;
	end for;
	D := ResidualIntersection(C, RS, R, E cat P[[3]] cat B, c, 3 - van_ord : eps := eps, PointsInRS := false);
	for i in [1..van_ord] do
		Append(~D, Coordinates(P[3])[[1,2]]);
	end for;
	if not(Correction) then
		return [RS!x : x in D];
	end if;
	// Step 3: Use Newton-Raphson with the Abel-Jacobi map to correct potential errors
	L := P[[1..3]] cat P[[1..3]];
	R := D1 cat D2;
	if Type(AJ1) eq SeqEnum then
		AJ1 := &+[AbelJacobi(L[i], R[i]) : i in [1..6]];
	end if;
	assert(#L eq 6);
	assert(#R eq 6);
	f := ToAnalyticJacobianFunction(C, RS : Q := P[[1..3]], Rs := D);
	D_Newt := Matrix([ [x[1]] : x in D ]);
	AJ2 := f(D_Newt);
	AJs_error, AJ_diff := EqualModPeriods(BigPeriodMatrix(RS), AJ1, AJ2); // It could happen that the answers are off by some integer multiples of the periods, here we correct for that.
	assert(AJs_error lt eps);
	AJ3 := AJ1 - AJ_diff;
	print "Difference between Abel-Jacobi's:", AJ3 - AJ2;
	f := ToAnalyticJacobianFunction(C, RS : Q := P[[1..3]], Rs := D, Goal := AJ3);
	df := JacobianDerivativeFunction(C, RS, [Coordinates(x)[[1..2]] : x in P[[1..3]]] : Rs := D);
	Dx_corr := NewtonRaphson(f, D_Newt : df := df, fx0 := AJ2 - AJ3, prec := 200, Verbose := true);
	d := &+[ Abs(D_Newt[i][1]-Dx_corr[i][1]) : i in [1..3] ];
	print "There was an error of", d;
	assert(d lt eps);
	D_corr := [RS!CloseComplexPoint(C, Dx_corr[i][1], D[i][2]) : i in [1..#D]];
	return D_corr;
end function;

function FindGoodBasePoints(C, RS : prec := 200)
	BestL := [];
	MaxDet := 0;
	for j in [1..100] do
		L := [ RandomComplexPoint(C, ComplexField(prec)) : i in [1..3] ];	
		df := JacobianDerivativeFunction(C, RS, L);
		M := df(Matrix([ [L[i][1]] : i in [1..3] ]));
		if Abs(Determinant(M)) gt MaxDet then
			MaxDet := Abs(Determinant(M));
			BestL := L;
		end if;
	end for;
	return [RS!x : x in BestL], MaxDet;
end function;

function ConvertToOtherBasis(C, RS, P, Q, E)
	// Trying similar strategy to usual addition algorithm to convert form E - P to D - Q for some D  
	FF := ComplexField(Precision(RS));
	eps := 10^-Floor(Precision(RS)/2);
	R<x,y> := PolynomialRing(FF, 2);
	// Step -1: find a random point B
	B := [RS!RandomComplexPoint(C, FF)];
	// Step 0a: find line through P1, P2
	c := Interpolate(C, R, P[[1,2]], 1);
	// Step 0b: find residual intersection A of line with C
	A := ResidualIntersection(C, RS, R, P[[1,2]], c, 2 : eps := eps);	
	// Step 1a: find a cubic through E, Q, A, B
	c := Interpolate(C, R, E cat Q cat A cat B, 3);
	// Step 1b: find residual intersection F of cubic with C
	F := ResidualIntersection(C, RS, R, E cat Q cat A cat B, c, 3 : eps := eps, AllowInfinity := true);
	// Step 2a: find a conic through F, P3, B
	c := Interpolate(C, R, F cat P[[3]] cat B, 2 : BasePt := Q[1]);
	// Step 2b: find residual divisor D of conic with C
	D := ResidualIntersection(C, RS, R, F cat P[[3]] cat B, c, 3 : eps := eps, AllowInfinity := true, PointsInRS := false, BasePt := Q[1]);
	D_FF := [ [FF!b : b in a] : a in D];
	return D_FF;
end function;

function InvertAbelJacobi(C, RS, v, B : prec := 200, L := [])
	n := 14;
	repeat
		n +:= 1;
		if #L eq 0 then
			L := FindGoodBasePoints(C, RS : prec := prec);
		end if;
		w := 2^(-n)*v;
		Rs := [Coordinates(x)[[1,2]] : x in L];
		f := ToAnalyticJacobianFunction(C, RS : Q := L, Rs := Rs, Goal := w);
		df := JacobianDerivativeFunction(C, RS, Rs);
		x0 := Matrix([ [Coordinates(x)[1]] : x in L]);
		try
			w_an := NewtonRaphson(f, x0 : df := df, Verbose := true);
			Succeeded := true;
		catch e
			Succeeded := false;
			assert(n lt 25);
		end try;
	until Succeeded;
	print "Found analytic solution for 1/", 2^n, "times vector";
	w_RS := [RS!CloseComplexPoint(C, w_an[i][1], Rs[i][2]) : i in [1..3]];
	for j in [1..n] do
		print j, "th doubling step";
		if j ne n then
			new_RS := FastAddition(C, RS, L, w_RS, w_RS : Correction := false); // : AJ1 := 2^(j-n)*v);
		else
			new_RS := FastAddition(C, RS, L, w_RS, w_RS : AJ1 := v);
		end if;
		w_RS := new_RS;
	end for;
	return ConvertToOtherBasis(C, RS, L, B, w_RS);
end function;


function ApproximatePolynomial(p : MaxDegree := 13)
	L := [];
	// First remove almost zero coefficients
	C := Coefficients(p);
	M := Monomials(p);
	for i in [1..#C] do
		eps := 10^-Floor(Precision(C[i])/4);
		if Abs(C[i]) lt eps then
			p -:= C[i]*M[i];
		end if;
	end for;
	// Then try to find algebraic relations for the other coefficients
	for i in [1..#Coefficients(p)] do
		c := Coefficients(p)[i];
		prec := Precision(Parent(c));
		c := ComplexField(Floor(0.95*prec))!c; 	// Get rid of last 5% of digits as they might be incorrect
		m := Exponents(Monomials(p)[i]);
		f := MinimalPolynomial(c, MaxDegree);
		if Degree(f) eq MaxDegree then
			return -1;
		end if;
		Append(~L, < f, c, m >);
	end for;
	return L;
end function;

function ApproximatePolynomials(L : MaxDegree := 13, Debug := false);
	M := [];
	for p in L do
		a := ApproximatePolynomial(p : MaxDegree := MaxDegree);
		if Type(a) eq RngIntElt then
			assert(not(Debug));
			return -1;
		end if;
		Append(~M, a);
	end for;
	return M;
end function;

function MumfordRepresentation(Coords, xPol, yPol, zPol : MaxDegree := 13, Debug := false)
	x1, y1, x2, y2, x3, y3 := Explode(Coords);
	InterPol := Evaluate(Interpolation([x1,x2,x3], [y1,y2,y3]), xPol);
	L := [ (xPol-x1*zPol)*(xPol-x2*zPol)*(xPol-x3*zPol), Homogenization(yPol  - InterPol, zPol) ];
	for p in L do
		assert IsHomogeneous(p);
	end for;
	return ApproximatePolynomials(L : MaxDegree := MaxDegree, Debug := Debug);
end function;

function GeneralRepresentation(Coords : MaxDegree := 13)
	x1, y1, z1, x2, y2, z2, x3, y3, z3 := Explode(Coords);
	R := PolynomialRing(Rationals(), 12);
	I := &*[ ideal< R | [R.j * R.(3*i + j mod 3 + 1)  - R.(j mod 3 +1) * R.(3*i + j) : j in [1..3]] > : i in [1..3] ];
	S<x,y,z> := PolynomialRing(Parent(x1), 3);
	L := [Evaluate(g, [x, y, z, x1, y1, z1, x2, y2, z2, x3, y3, z3]) : g in Generators(I)];
	return ApproximatePolynomials(L : MaxDegree := MaxDegree);
end function;


intrinsic AnalyticTorsionSearch(C, RS, B, v2, l, lTorsion : MaxDegree := 13, Succeeded := [])->SeqEnum,BoolElt
{ Try to find torsion points using complex analytic methods. }
	prec := Precision(RS);
	M := BigPeriodMatrix(RS);
	N := Transpose(Transpose(Matrix(Transpose(M)[1..3]))^(-1)*M);
	DividingZero := false;
	v_tried := [];
	if #Succeeded eq 0 then
		Failed := [];
		for S in CartesianPower({0..l-1}, 6) do
			// When diving zero, we can assume the first non-zero entry to be 1.
			if DividingZero then
				for i in [1..6] do
					if S[i] eq 0 then
						continue i;
					elif S[i] eq 1 then
						break i;
					else
						continue S;
					end if;
				end for;
			end if;
		
			c := [S[i] : i in [1..6]];
			print c;
			v := v2/l + Transpose(Matrix(&+[c[i]*N[i]/l : i in [1..6]]));
			if &+[Abs(v[i][1]) : i in [1..3]] lt 10^-Floor(prec/2) then
				DividingZero := true;
				continue S;
			end if;
			
			// Compare v against previously tried v, when the difference is a known torsion element, do not try again.
			for w in v_tried do
				for t in lTorsion do
					if EqualModPeriods(M, v-w, t) lt 10^-Floor(prec/4) then
						//break w;
						continue S;
					end if;
				end for;
			end for;			
			Append(~v_tried, v);
			
			//try
				A := InvertAbelJacobi(C, RS, v, B : prec := prec);
				Append(~Succeeded, A);
			/*catch e
				print e;
				Append(~Failed, v);
			end try;*/
		end for;
		// Retry the failed ones in case of a unfortunate choice of random basis
		for v in Failed do
			//try
				A := InvertAbelJacobi(C, RS, v, B : prec := prec);
				Append(~Succeeded, A);
			/*catch e
				print e;
			end try;*/
		end for;
	end if;
	// Compute Mumford/general representation
	// Try to find minimal polynomials
	// Go up to degree 13, as it should suffice to search up to degree 12
	MumfordReps := [];
	MumfordSucceeded := [];
	R<x> := PolynomialRing(ComplexField(prec));
	for Pt in Succeeded do
		print "Point #", Index(Succeeded, Pt);
		PtRed := [ [x : x in Pt[i]] : i in [1..3]];
		for i in [1..3] do
			if #PtRed[i] eq 2 then
				Append(~PtRed[i], 1);
			end if;
		end for;
		A := PolynomialRing(Parent(PtRed[1][1]), 3);
		B := PolynomialRing(Rationals(), 3);
		EqPol := Evaluate(Equation(C), [B.1, B.2, B.3]);
		
		RepFound := false;
		Tried := 0;
		for Den in CartesianPower([0..1], 3) do
			DenPol := &+[A.i*Den[i] : i in [1..3]];
			DenPolB := &+[B.i*Den[i] : i in [1..3]];
			for x in PtRed do
				if Abs(Evaluate(DenPol, x)) lt 10^-Floor(prec/20) then
					continue Den;
				end if;
			end for;
			
			for Num in CartesianPower([0..2], 3) do
				if (GCD([Num[i] : i in [1..3]]) ne 1) or (Num eq Den) then
					continue Num;
				end if;
				NumPol := &+[A.i*Num[i] : i in [1..3]];
				NumPolB := &+[B.i*Num[i] : i in [1..3]];
				if Saturation(ideal< B | [EqPol, NumPolB, DenPolB] >) ne B then
					continue Num;
				end if;
				M := [ [Den[i] : i in [1..3]], [Num[i] : i in [1..3]] ];
				if Determinant(Matrix(Append(M, [1,0,0]))) ne 0 then
					NumPol2 := A.1;
				elif Determinant(Matrix(Append(M, [0,1,0]))) ne 0 then
					NumPol2 := A.2;
				elif Determinant(Matrix(Append(M, [0,0,1]))) ne 0 then
					NumPol2 := A.3;
				else
					assert(false);
				end if;
				EvalValues := [];
				for x in PtRed do
					xValue := Evaluate(NumPol, x) / Evaluate(DenPol, x);
					for y in EvalValues do
						if Abs(xValue - y[1]) lt 10^-Floor(prec/20) then
							continue Num;
						end if;
					end for;
					yValue := Evaluate(NumPol2, x) / Evaluate(DenPol,x);
					Append(~EvalValues, [xValue, yValue]);
				end for;
				
				if Degree(MinimalPolynomial(ComplexField(Floor(0.95*Precision(Parent(EvalValues[1][1]))))!&*[a[1] : a in EvalValues], MaxDegree)) eq MaxDegree then
					//print "Skipping Mumford representation", Mum, Den;
					continue Num;
				end if;
				
				print "Trying Mumford representation", Num, Den;
				Tried +:= 1;
				Mf := MumfordRepresentation(&cat EvalValues, NumPol, NumPol2, DenPol : MaxDegree := MaxDegree);
				if Type(Mf) ne RngIntElt then
					print "Mumford representation found";
					RepFound := true;
					Append(~MumfordReps, Mf);
					Append(~MumfordSucceeded, Pt);
					break Den;
				end if;
				if Tried ge 20 then
					break Den;
				end if;
				continue Den;
				
			end for; //Num
		end for; //Den
			
			
		if not(RepFound) then	
			// General case: should only happen when two points collide.		
			Mf := GeneralRepresentation(&cat PtRed : MaxDegree := MaxDegree);
			print "General representation found";
			if Type(Mf) ne RngIntElt then
				print "added";
				Append(~MumfordReps, Mf);
				Append(~MumfordSucceeded, Pt);
			end if;
		end if;
		
		
		
	end for;
	assert(#MumfordReps gt 0);
	return MumfordReps, MumfordSucceeded;
end intrinsic;
