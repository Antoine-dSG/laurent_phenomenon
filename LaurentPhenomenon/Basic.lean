import Mathlib.Data.Matrix.Basic
inductive myProd1 where
  | building_a_pair : Int → Int → myProd1

#check myProd1.rec

inductive myProd1' where
  | building_a_pair (a : Int) (b : Nat) : myProd1'

inductive myProd1'' where
  | building_a_pair (b : Nat) (a : Int) : myProd1''

#check myProd1'.building_a_pair (-3)
#check myProd1''.building_a_pair 3

inductive myProd2 (α: Type 0) where
  | building_a_pair : (a : α) → Int → myProd2 α



#check myProd1.building_a_pair 1 2
-- #check myProd1.building_a_pair "hi" 2
#check myProd2.building_a_pair "hi" 2
#check False

variable (proof_of_equality : (1=2))
-- #check myProd2.building_a_pair (proof_of_equality) 2

#check Bool.rec

inductive myProd3 (α : Type*) where
  | building_a_pair : (a : α) → Int → myProd3 α

def first_coord (p : myProd3 String) : String :=
  match p with
    | myProd3.building_a_pair a _ => a

#eval first_coord (myProd3.building_a_pair "happy" 3)

structure studentDetails where
  (firstName : String)
  (midlleName : String)
  (lastName : String)
  (UID : Int)

#check studentDetails.mk "hi" "how" "are" 2

structure myFiniteSet where
  (n : Int)
  (val : Int)
  (isLT : LT.lt val n)


inductive myList (n : Nat) where
  | empty : myList n
  | build (L : myList n) (i : Nat) (a : i < n) : myList n

def tail_of_myList {n : Nat} (L : myList n) : Option Nat :=
  match L with
    | myList.empty => none
    | myList.build _ i _=> some i

def a₀ := @myList.empty 4
def a₁ := myList.build a₀ 1 (by simp)
def a₁₂ := myList.build a₁ 2 (by simp)
def a₁₃ := myList.build a₁ 3 (by simp)
def a₁₁ := myList.build a₁ 1 (by simp)
def a₂ := myList.build a₀ 2 (by simp)
def a₃ := myList.build a₀ 3 (by simp)

#eval tail_of_myList a₃
#eval tail_of_myList a₁₂

inductive ValidList (n : Nat) : Option Nat → Type where
  | nil : ValidList n none
  | cons (k : Nat) (hk : 1 ≤ k ∧ k ≤ n) {last : Option Nat} (tail : ValidList n last) (h_ne : k ≠ last.getD 0) : ValidList n (some k)

#check @ValidList.nil 5
def b₁ := @ValidList.cons 5 1 (by simp) (none) ValidList.nil (by simp)
def b₁₂ := @ValidList.cons 5 2 (by simp) (some 1) b₁ (by simp)


def tail {n : Nat} (L : ValidList n a) : Option Nat :=
  match L with
    | ValidList.nil => none
    | ValidList.cons k _ _ _=> some k

#eval tail b₁
#eval (tail b₁₂)

def ValidList.length {n : Nat} {last : Option Nat} (l : ValidList n last) : Nat :=
  match l with
  | .nil => 0
  | .cons _ _ t _ => 1 + t.length

#eval ValidList.length (@ValidList.nil 5)

def mat1 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun m n =>
    match (m.1, n.1) with
    | (0,1) => 1
    | (1,0) => -1
    | _ => 0

#eval mat1

def tree_to_mylist (M : Matrix (Fin 2) (Fin 2) ℤ) (L : myList 4) : List (Matrix (Fin 2) (Fin 2) ℤ) :=
  match L with
    | myList.empty => [M]
    | myList.build star k _ => k*M :: tree_to_mylist M star

#eval tree_to_mylist mat1 a₁₂

-- The type is List Fin n
#check @Fin.mk 17 2 (by simp)
#eval @Fin.mk 17 2 (by simp)

def a₂₄ := @Fin.mk 17 2 (by simp) :: (@Fin.mk 17 4 (by simp)) :: []
#check a₂₄

def list_to_mat (M : Matrix (Fin 2) (Fin 2) ℤ) (L : List (Fin 17)) : List (Matrix (Fin 2) (Fin 2) ℤ) :=
  match L with
    | List.nil => [M]
    | x::xs => ((x.1)*M) :: list_to_mat M xs

#check list_to_mat mat1 a₂₄
#eval list_to_mat mat1 a₂₄
