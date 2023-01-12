function FakeStabiliser(H)
	C := ConjugacyClasses(H);
	G := Infinity();
	for c in C do
		M := c[3];
		if Type(H) eq GrpMat then
			G := Min(G, Dimension(Eigenspace(M, 1)));
		elif Type(H) eq GrpPerm then
			G := Min(G, #Fix(M));
		else
			assert(false);
		end if;
	end for;
	return G;
end function;

function RealStabiliser(H)
	if Type(H) eq GrpMat then
		if IsTrivial(H) then
			return 6;
		end if;
		return Dimension(&meet[Eigenspace(V,1) : V in Generators(H)]);
	elif Type(H) eq GrpPerm then
		return #Fix(H);
	end if;
	assert(false);
end function;

function WorstRootDegree(H)
	AllRoots := [x : x in Set(&join Orbits(H))];
	RootDegrees := [Index(H, Stabiliser(H, x)) : x in AllRoots];
	AllDegrees := Sort([ x : x in Set(RootDegrees)]);
	HEigenspaces := [a : a in {Eigenspace(M[3],1) : M in ConjugacyClasses(H)}];
	for d in [0] cat AllDegrees do
		RootsConsidered := [AllRoots[i] : i in [1..#AllRoots] | RootDegrees[i] le d];
		for j in [1..#HEigenspaces] do
			if Dimension(sub<HEigenspaces[j] | [y : y in RootsConsidered | y in HEigenspaces[j]]>) ge Dimension(HEigenspaces[j]) then
				return d;
			end if;
		end for;
	end for;
	assert(false);
end function;

function FixedPerms(a)
	return {Random(x) : x in CycleDecomposition(a) | #x eq 1};
end function;

function AffineWorstRootDegree(H)
	AllRoots := [x : x in Set(&join Orbits(H))];
	RootDegrees := [Index(H, Stabiliser(H, x)) : x in AllRoots];
	AllDegrees := Sort([ x : x in Set(RootDegrees)]);
	Stabilisers := [ FixedPerms(a[3]) : a in ConjugacyClasses(H)];
	for d in [0] cat AllDegrees do
		RootsConsidered := {AllRoots[i] : i in [1..#AllRoots] | RootDegrees[i] le d};
		for j in [1..#Stabilisers] do
			if Stabilisers[j] subset RootsConsidered then
				return d;
			end if;
		end for;
	end for;
	assert(false);
end function;

print "GSp(6, 2)";
G := ConformalSymplecticGroup(6, 2);
I := [H`subgroup : H in Subgroups(G) | RealStabiliser(H`subgroup) ne FakeStabiliser(H`subgroup) ];
L := {* WorstRootDegree(H) : H in I *};
print L; // {* 2^^276, 3^^49, 4^^14, 6^^19, 8, 10^^5, 12^^4 *}

print "GSp(6, 3)";
G := ConformalSymplecticGroup(6, 3);
I := [H`subgroup : H in Subgroups(G) | RealStabiliser(H`subgroup) ne FakeStabiliser(H`subgroup) ];
L := {* WorstRootDegree(H) : H in I *};
print L; // {* 2^^3892, 3^^677, 4^^153, 6^^273, 8^^106, 9^^9, 12 *}

print "G < AffSp(6,2)";
G := Stabiliser(AffineSymplecticGroup(6, 2), { {2*i-1,2*i} : i in [1..32] });
I := [H`subgroup : H in Subgroups(G) | RealStabiliser(H`subgroup) ne FakeStabiliser(H`subgroup) ];
L := {* AffineWorstRootDegree(H) : H in I *};
print L; // {* 2^^2392, 3^^24, 4^^543, 6^^68, 8^^31, 10^^12, 12^^27 *}
