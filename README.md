# Insertion Sort Correctness Proofs in Lean: A Comparison of Different Specifications

This repository contains correctness proofs for **Insertion Sort** under different specifications in Lean.  
The goal is to compare how different specifications affect the structure and difficulty of correctness proofs.  
This work was inspired by [Verified Functional Algorithms](https://softwarefoundations.cis.upenn.edu/vfa-current/toc.html) of Software Foundations. For more details, see the accompanying paper [Insertion_Sort.pdf](https://github.com/jeinryu/InsertionSort/blob/main/Insertion_Sort.pdf)

A correctness proof for a sorting algorithm typically involves these two properties:

1. **Sortedness:** The output list is sorted.  
2. **Content Preservation:** The output list contains the same elements as the original list.

We provide two different specifications for each property and prove correctness under each specification.  Here is the overall structure:



## 1. Proof of Sortedness

1. **Inductive Definition**  
   File: [InductiveProof.lean](InsertionSort/InductiveProof.lean)  
   Inductive predicate describing sortedness

2. **Index-Based Definition**  
   File: [IndexProof.lean](InsertionSort/IndexProof.lean)  
   A numeric formulation using `∀ i < j, l[i] ≤ l[j]`

3. **Equivalence of the Two Definitions**  
   File: [SortedEq.lean](InsertionSort/SortedEq.lean)  



## 2. Proof of Content Preservation

1. **Permutation-Based Proof**  
   File: [PermProof.lean](InsertionSort/PermProof.lean)  
   Uses Permutation relation

2. **Multiset-Based Proof**  
   File: [MultisetProof.lean](InsertionSort/MultisetProof.lean)  
   Uses the equality of multisets

3. **Equivalence of the Two Approaches**  
   File: [PermEq.lean](InsertionSort/PermEq.lean)  


## References

  *Software Foundations, Volume 3: Verified Functional Algorithms*  
  Andrew W. Appel et al.  
  [https://softwarefoundations.cis.upenn.edu/vfa-current/toc.html](https://softwarefoundations.cis.upenn.edu/vfa-current/toc.html)  