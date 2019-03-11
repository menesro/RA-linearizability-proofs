CRDTs are verified by Boogie (v.2.3.0.6106) and Z3 (v.4.8.0 64-bit ) as the underlying SMT solver. 
For installing Boogie and installation instructions, please visit:
https://github.com/boogie-org/boogie

For installing Z3 and installation instructions, please visit:
https://github.com/Z3Prover/z3

Each file is verified using a plain Boogie call without using any flags i.e. "Boogie file_path".

Verification tasks are run on an Intel i7-7700HQ 2.8GHz machine with 16 GB RAM. Verification of each file took less than a minute.

Proof of each op-based CRDT c is divided into two files. alias(c)_Ref_Boogie.bpl proves that all the effectors and generators of c preserves the refinement relation. Whereas, alias(c)_Com_Boogie.bpl shows that the effectors of c commute with respect to each other.

For the state based CRDTs, proof is divided into two files as well. alias(c)_Prop_Boogie.bpl proves that c satisfies properties prop1 to prop5 (or to prop6 if c is of second case and satisfies C1). On the other hand alias(c)_Ref_Boogie.bpl again shows that all the effectors and generators of c preserves the refinement relation.

alias(c) is a function that changes the name of a CRDT to the one that we use in the proof files. It is defined as:
2 Phase set --> 2PSet
Counter --> Ctr
Last Writer Wins Register --> LWWReg
Last Writer Wins Element Set --> LWWSet
Multi-Value Register --> MVReg
OR Set --> ORSet
PN Counter --> PNCounter
RGA --> RGA
Wooki --> Wookie