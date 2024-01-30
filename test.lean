inductive MyNat where
  | zero: MyNat
  | succ (n : MyNat) : MyNat

def lte (n1 : MyNat) (n2 : MyNat) : Bool :=
  match n1 with
  | MyNat.zero => true
  | MyNat.succ n1' =>
    match n2 with
    | MyNat.zero => false
    | MyNat.succ n2' => lte n1' n2'

inductive MyList (α : Type) where
  | nil: MyList α
  | cons: α → MyList α → MyList α

def sorted (list : MyList MyNat) : Bool :=
  match list with
  | MyList.nil => true
  | MyList.cons _ MyList.nil => true
  | MyList.cons a (MyList.cons b tail) =>
    lte a b ∧ sorted (MyList.cons b tail)

def one := MyNat.succ MyNat.zero
def two := MyNat.succ one

#check sorted (MyList.cons one (MyList.cons two MyList.nil))

#check And.left

theorem monotonic_increase : sorted (MyList.cons a (MyList.cons b tail)) → lte a b := by
  unfold sorted
  simp
  apply And.left

theorem carry_sorted : sorted (MyList.cons a (MyList.cons b tail)) → sorted (MyList.cons a tail) := by
  admit


theorem sublist_sorted : ∀ a tail, sorted (MyList.cons a tail) → sorted tail := by
  intro a tail
  induction tail with
  | nil =>
    unfold sorted
    simp
  | cons head tail' ih =>
    intro foo





def insert_sorted (list : MyList MyNat) (is_sorted : sorted list) (element : MyNat) : MyList MyNat :=
  match list with
  | MyList.nil => MyList.cons element MyList.nil
  | MyList.cons head tail =>
      if lte element head then
        MyList.cons element list
      else
        let tail_sorted := sublist_sorted is_sorted
        MyList.cons head (insert_sorted tail tail_sorted element)
