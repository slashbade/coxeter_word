import Std.Data.List.Basic

def hello := "world"

inductive S : Type :=
  | a : S
  | b : S
  | c : S
  deriving Repr

#eval S.a

instance : BEq S where
  beq := fun x y => match x, y with
  | S.a, S.a => true
  | S.b, S.b => true
  | S.c, S.c => true
  | _, _ => false

instance : Inhabited S where
  default := S.a

structure BraidRelation where
  s1 : S
  s2 : S
  m12 : Nat

-- Primitive way to define a Coxeter System
def br12 : BraidRelation := { s1 := S.a, s2 := S.b, m12 := 5 }
def br13 : BraidRelation := { s1 := S.a, s2 := S.c, m12 := 2 }
def br23 : BraidRelation := { s1 := S.b, s2 := S.c, m12 := 3 }
def br21 : BraidRelation := { s1 := S.b, s2 := S.a, m12 := 5 }
def br31 : BraidRelation := { s1 := S.c, s2 := S.a, m12 := 2 }
def br32 : BraidRelation := { s1 := S.c, s2 := S.b, m12 := 3 }


def brs : List BraidRelation := [br12, br23, br13, br21, br31, br32]


open S

def w : List S := [a, b, c, c, b, a, b, a, b, a]


def nil_move : List S → List S :=
  fun l => match l with
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    match x == y with
    | true => nil_move xs
    | false => x :: nil_move (y :: xs)


def pattern (s1 : S) (s2 : S) (m12 : Nat) : S × List S × List S :=
  match m12 with
  | 0 => (s1, [], [])
  | 1 => (s2, [s1], [s2])
  | n + 1 =>
    let (s, p1, p2) := pattern s1 s2 n
    match s == s1 with
    | true => (s2, s1 :: p1, s2 :: p2)
    | false => (s1, s2 :: p1, s1 :: p2)



#eval pattern a b 5


def braid_move_aux (pattern1 : List S) (pattern2 : List S) (pattern_length : Nat) : List S → List S :=
  fun l => match l with
  | [] => []
  | [x] => [x]
  | x :: xs =>
    match l.take pattern_length == pattern1 with
    | true => pattern2 ++ l.drop pattern_length
    | false => x :: braid_move_aux pattern1 pattern2 pattern_length xs


def braid_move (br : BraidRelation) : List S → List S :=
  fun l =>
    let (_, p1, p2) := pattern br.s1 br.s2 br.m12
    braid_move_aux p1 p2 p1.length l

def braid_move_Nth (br : BraidRelation) (w : List S) (n : Nat) : List S :=
  match n with
  | 0 => braid_move br w
  | n + 1 => match w with
    | [] => []
    | x :: xs =>
      let p1 := (pattern br.s1 br.s2 br.m12).2.1
      match w.take p1.length == p1 with
      | true => x :: (braid_move_Nth br xs n)
      | false => x :: (braid_move_Nth br xs (n+1))


def w1 := [a, b, a, b, a, b, a, b]

#eval braid_move_Nth br12 w1 3
#eval w.removeNth 3

def w2 := [c, c, b,b, c, c, c]
#eval nil_move w2

#eval nil_move (braid_move br12 (nil_move (braid_move br12 w)))


#eval (nil_move ∘ nil_move) w


def nil_move_rec (w : List S) : List S :=
  if (nil_move w).length < w.length then
    nil_move_rec (nil_move w)
  else w
  termination_by w.length


#eval nil_move_rec w

-- to obtain all words that can be obtained by sequences of braid moves and nil_moves
-- this is a halt algorithm, well-founded property can be parametrized by a tuple (length_no, perm_no)
partial def WD (w : List S) (brl : List BraidRelation) (n_pos : Nat) : List (List S) :=
  match brl with
  | [] => [w]
  | brh :: brt =>
    let w' := nil_move_rec (braid_move_Nth brh w n_pos)
    match w == w' with
    | true =>
      let w'' := nil_move_rec (braid_move_Nth brh w (n_pos + 1))
      match w == w'' with
      | true =>
        WD w brt 0
      | false => w :: WD w'' brt 0
    | false => w :: WD w' brl 0

def length_fun (w : List S) (brl : List BraidRelation) := (WD w brl 0).getLast!.length

-- to obtain list of all reduced words from list of all obtainable words
def RD (w : List S) (brl : List BraidRelation) : (List (List S)) :=
  let wds := WD w brl 0
  wds.filter (fun w => w.length == wds.getLast!.length)


#eval WD w brs 0

def w3 := [c, b, c, a, c, b, a, b, a, c, b, b, a, c, b]

#eval braid_move_Nth br23 w3 0
#eval WD w3 brs 0
#eval pattern brs[0].s1 brs[0].s2 brs[0].m12
