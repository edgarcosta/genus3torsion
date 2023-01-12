Dependencies

For this package to work, you need to have installed PARI/GP, which should run using the command 'gp', or otherwise the file 'polredabs.m' needs to be modified.
You also need to compile the program 'myfrob' in the package 'controlledreduction-torsion', which can be found at https://github.com/rbommel/controlledreduction-torsion.

Installation

On the first line of 'Torsion.m', you need to set 'MyFrobCommand' to whatever command you use to run 'myfrob'. In my case this was 'export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/sage/sage-9.5/local/lib/; /home/bommel/cap/controlledreduction-torsion/build/examples/myfrob', but this might be different on your machine.

Intrinsics

The following intrinsics are available:
* TorsionSubgroup: main intrinsic of this package
* Torsion: a wrapper for TorsionSubgroup
* ConvertProofToList: converts proof data to an easily storable list format
* ConvertListToProof: converts list to proof data
* VerifyProof: verifies proof for the torsion group
* VerifyListProof: verify proof stored in list format

As a side product this package also contains an implementation of (naive) Jacobian arithmetic for (non-hyperelliptic) curves, which could be used independently of the torsion computation.
