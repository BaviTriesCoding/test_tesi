import DeductionTreeWidget.DeductionTreeWidget
import Lean
open Lean
open Lean.Elab.Tactic

namespace matita

syntax "_last_hypothesis_" : term

elab_rules : term
 |`(term| _last_hypothesis_) => do ((← Lean.getLCtx).lastDecl.map (fun x ↦ x.toExpr)).getM -- bug here exclude recursive call to theorem

declare_syntax_cat matitaEquivalent

syntax "that " "is " "equivalent " "to " term : matitaEquivalent

syntax "assume " ident " : " term (matitaEquivalent)? : tactic

macro_rules
  | `(tactic| assume $ident : $type) => `(tactic| intro $ident:ident <;> guard_hyp _last_hypothesis_ :ₛ $type)
  | `(tactic| assume $ident : $type that is equivalent to $type₂) =>
    `(tactic| assume $ident : $type <;> have $ident := @id $type₂ $ident)


syntax "suppose " term (matitaEquivalent)? (" as " ident)? : tactic

macro_rules
  | `(tactic| suppose $term as $ident) => `(tactic| intro $ident:ident <;> guard_hyp _last_hypothesis_ :ₛ $term)
  | `(tactic| suppose $term) => `(tactic| intro <;> guard_hyp _last_hypothesis_ :ₛ $term)
  | `(tactic| suppose $term that is equivalent to $type ) =>
    `(tactic| suppose $term <;> let _ := @id $type _last_hypothesis_)
  | `(tactic| suppose $term that is equivalent to $type as $ident ) =>
    `(tactic| suppose $term as $ident <;> let $ident := @id $type $ident)


-- one more bug here
--macro_rules
--  | `(matitaJust | by ) =>
--    `(Lean.Parser.Tactic.SolveByElim.arg | [])

theorem iff_e: ∀A B: Prop, (A ↔ B) → (A → B) ∧ (B → A) := by
 intros A B U ; cases U ; constructor <;> solve_by_elim

declare_syntax_cat matitaJust

syntax "thus "? ("by " ident,+)? : matitaJust

-- simplify the code now that after by the list must be non empty?
-- factorize Or.inr/Or.inl
def matitaJust_to_solveByElimArg : TSyntax `matitaJust -> MacroM (TSyntax ``Lean.Parser.Tactic.SolveByElim.args)
  | `(matitaJust | thus by $[$terms],* ) => do
    let args ← terms.mapM fun x => `(Lean.Parser.Tactic.SolveByElim.arg| $x:ident)
    `(Lean.Parser.Tactic.SolveByElim.args| [$(args.push (← `(Lean.Parser.Tactic.SolveByElim.arg| _last_hypothesis_))),*, Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(matitaJust | by $[$terms],* ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [$[$terms:ident],*, Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(matitaJust | thus ) =>
    `(Lean.Parser.Tactic.SolveByElim.args| [_last_hypothesis_, Or.inr, Or.inl, matita.iff_e, And.left, And.right])
--  | `(matitaJust | ) =>
--    `(Lean.Parser.Tactic.SolveByElim.args| [])
  | _ => -- panic! "xxx" -- thereis  the right throwXXX
    `(Lean.Parser.Tactic.SolveByElim.args| [Or.inr, Or.inl, matita.iff_e, And.left, And.right])

syntax matitaJust " done" : tactic

macro_rules
  | `(tactic | $mj:matitaJust done) => do
    `(tactic | solve_by_elim only $(← matitaJust_to_solveByElimArg mj))
  | `(tactic | done) => do
    `(tactic | solve_by_elim only [Or.inr, Or.inl, matita.iff_e, And.left, And.right])

syntax (matitaJust)? "we " " proved " term ("as " ident)? : tactic
syntax (matitaJust)? "we " " proved " term "as " ident "and " term "as " ident : tactic
syntax (matitaJust)? "let " ident ": " term "such " "that " term "as " ident : tactic

-- duplicated code, not nice
-- idea: factorize a bit using a _empty_matita_just ?  or just use obviously?
macro_rules
  | `(tactic | $mj:matitaJust we proved $term as $ident) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have $ident : $term := by solve_by_elim only $x)
  | `(tactic | $mj:matitaJust we proved $term) => do
    let x ← matitaJust_to_solveByElimArg mj
    `(tactic | have _ : $term := by solve_by_elim only $x)
  | `(tactic | we proved $term as $ident) =>
    `(tactic | have $ident : $term := by solve_by_elim only [Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(tactic | we proved $term) =>
    `(tactic | have _ : $term := by solve_by_elim only [Or.inr, Or.inl, matita.iff_e, And.left, And.right])
  | `(tactic | $mj:matitaJust we proved $term₁ as $ident₁ and $term₂ as $ident₂) =>
    `(tactic | $mj:matitaJust we proved $term₁ ∧ $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)
  | `(tactic | we proved $term₁ as $ident₁ and $term₂ as $ident₂) =>
    `(tactic | we proved $term₁ ∧ $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)
  | `(tactic | $mj:matitaJust let $ident₁ : $term₁ such that $term₂ as $ident₂) =>
    `(tactic | $mj:matitaJust we proved ∃$ident₁:ident : $term₁, $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)
  | `(tactic | let $ident₁ : $term₁ such that $term₂ as $ident₂) =>
    `(tactic | we proved ∃$ident₁:ident : $term₁, $term₂ <;> cases _last_hypothesis_ <;> case' _ $ident₁:ident $ident₂:ident => skip)

syntax "we " "need " "to " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic | we need to prove $term) =>
  `(tactic | guard_target =ₛ $term)
 | `(tactic | we need to prove $exp that is equivalent to $inf) =>
  `(tactic | we need to prove $exp <;> change $inf)

macro "we " "split " "the " "proof " : tactic => `(tactic| first | apply And.intro | apply Iff.intro)

macro "we " "claim " stmt:term "as " name:ident "by" colGt prf:tacticSeq : tactic => `(tactic|have $name : $stmt := by $prf)
macro "we " "claim " stmt:term                  "by" colGt prf:tacticSeq : tactic => `(tactic|have _ : $stmt := by $prf)

syntax "by " term "it " "suffices " "to " "prove " term : tactic -- "it suffices to prove " is a keyword in Verbose

macro_rules
 | `(tactic| by $term:term it suffices to prove $arg) => `(tactic| apply $term:term <;> we need to prove $arg:term)

syntax "we " "choose " term "and " "prove " term (matitaEquivalent)? : tactic

macro_rules
 | `(tactic| we choose $term₁ and prove $term₂) => `(tactic| exists $term₁ <;> we need to prove $term₂)
 | `(tactic| we choose $term₁ and prove $term₂ that is equivalent to $term₃) =>
   `(tactic| we choose $term₁ and prove $term₂ <;> change $term₃)

macro "we " "proceed " "by " "cases " "on " name:ident "to " "prove " stmt:term : tactic => `(tactic|guard_target =ₛ $stmt <;> cases $name:term)

macro "we " "proceed " "by " "cases " "on " "the " "guard " t:term : tactic => `(tactic|cases $t:term)

macro "we " "proceed " "by " "induction " "on " name:ident ": " type:term "to " "prove " stmt:term : tactic => `(tactic|guard_target =ₛ ∀$name : $type, $stmt <;> intro $name:ident <;> induction $name:term)

syntax "guard_hyps" "[" ("( " ident ": " term ") ")* "]" : tactic

macro_rules
 | `(tactic| guard_hyps []) => `(tactic| skip)
 | `(tactic| guard_hyps [($id : $term) $[($ids : $terms)]*]) => `(tactic| guard_hyp $id :ₛ $term <;> guard_hyps [$[($ids : $terms)]*])

syntax "case " ident
       ("( " ident ": " term ") ")*
       ("by " "induction " "hypothesis " "we " "know " term "as " ident)* : tactic

macro_rules
 | `(tactic| case $name:ident $[( $arg:ident : $type:term )]*
      $[by induction hypothesis we know $iitype:term as $ii:ident]*) =>
   `(tactic| case' $name:ident $[$arg:ident]* $[$ii:ident]* => guard_hyps [$[($arg : $type)]* $[($ii : $iitype)]*])

end matita
show_panel_widgets [NDTreeJsonViewerWidget]

section lab_recursion_induction_2024_12_11

-- Problema: una lista di booleani si dice alternating quando due booleani consecutivi nella
-- lista sono uno il negato dell'altro
-- Esempi:
--  [true,false,true,false,true] è alternating
--  [true,false,false,true,false] non è alternating

-- Esercizio 1: implementare con la ricorsione strutturale una funzione alternating che
-- dica se una lista in input è alternating
-- Per risolvere l'esercizio implementare una seconda funzione keep_alternating che prende in
-- input come secondo argomento un accumulatore che ricorda qual'è l'ultimo booleano incontrato
-- keep_alternating l b  deve restituire true sse la lista b::l è alternating
-- SUGGERIMENTI:
--   i booleani si scrivono true e false
--   not è la negazione sui booleani e && è la congiunzione sui booleani
def keep_alternating: List Bool -> Bool -> Bool
| [], _acc => true
| b::l, acc => b = not acc && keep_alternating l b

-- SUGGERIMENTI:
--  utilizzare la funzione keep_alternating
--  non è obbligatorio fare chiamate ricorsive
def alternating: List Bool -> Bool
| [] => true
| b::l => keep_alternating l b

theorem test_alternating:
 alternating [true,false,true,false,true] = true ∧
 alternating [true,false,false,true,false] = false ∧
 alternating [] = true
:= by simp!
#check test_alternating

-- Esercizio 2: implementare una funzione alternating' con la stessa specifica di alternating, ma
-- senza usare la tecnica dell'accumulatore
-- Per farlo serve implementare una funzione starts_with che prende una lista di booleani l
-- e un booleano b e restituisce true quando se la lista è non vuota allora il suo primo elemento è b
def starts_with: List Bool -> Bool -> Bool
| [], _b => true
| x::_l, b => x=b

-- SUGGERIMENTO:
--  richiamare la funzione starts_with con gli input appropriati
def alternating' : List Bool -> Bool
| [] => true
| x::l => starts_with l (not x) && alternating' l

theorem test_alternating':
 alternating' [true,false,true,false,true] = true ∧
 alternating' [true,false,false,true,false] = false ∧
 alternating' [] = true
:= by simp!
#check test_alternating'

------------------------------------------

-- Ignorare le seguenti due righe che
--  1. attivano la sintassi usuale per l'if-then-else, ovvero
--      if GUARDIA then ESPRESSIONE₁ else ESPRESSIONE₂
--  2. definiscono ≤ come la funzione che dati due naturali restituisce un booleano
macro_rules
  | `(if $c then $t else $e) => `(cond $c $t $e)
infix:50 (priority := high)" ≤ "  => Nat.ble

-- Esercizio 3: l'obiettivo è implementare una funzione sort che ordini una lista di naturali
-- in maniera crescente
-- SUGGERIMENTI:
--  per definire la sort dovrete implementare una seconda funzione insert
--  prima di implementare la insert dovete capire bene cosa deve fare, riflettendo sul caso
--  induttivo della sort. Di fatto iniziate prima a scrivere la sort e poi tornate alla insert

-- ATTENZIONE: Completate la seguente specifica (il commento) della insert
-- insert l n
--   data una lista l con la proprietà di essere ordinata
--   e dato un intero n
--   restituisce la lista ottenuta inserendo n in l garantendo la proprietà di essere ordinata
def insert: List Nat -> Nat -> List Nat
| [],x => [x]
| y::l,x => if x ≤ y then x::y::l else y::insert l x

def sort: List Nat -> List Nat
| [] => []
| x::l => insert (sort l) x

theorem test_sort:
 sort [] = [] ∧
 sort [3,2,1,5,3,17] = [1,2,3,3,5,17]
:= by simp!
#check test_sort

-- Esercizi 4 e 5: vogliamo dimostrare che la funzione sort restituisce una lista che ha la stessa
-- lunghezza di quella presa in input. Per fare questo ci serve la definizione della lunghezza
-- di una lista e un lemma che dimostra che inserendo un elemento in una lista la lunghezza si
-- incrementa di 1

def length: List Nat -> Nat
| [] => 0
| _x::l => Nat.succ (length l)

-- Esercizio 4:
theorem insert_length: ∀l n, length (insert l n) = Nat.succ (length l) := by
 we proceed by induction on l : List Nat to prove
  ∀n, length (insert l n) = Nat.succ (length l)
 . case nil
   we need to prove ∀n, length (insert [] n) = Nat.succ (length [])
   that is equivalent to ∀n, 1 = 1
   done
 . case cons (y : Nat) (l: List Nat)
   by induction hypothesis we know ∀n, length (insert l n) = Nat.succ (length l) as IH
   we need to prove ∀n, length (insert (y::l) n) = Nat.succ (length (y::l))
   that is equivalent to
    ∀n, length (if n ≤ y then n::y::l else y::insert l n) = Nat.succ (Nat.succ (length l))
   assume n : Nat
   we proceed by cases on the guard n ≤ y  -- NUOVO COMANDO per lavorare per casi sugli if-then-else
   . case false
     we need to prove length (if false then n::y::l else y::insert l n) = Nat.succ (Nat.succ (length l))
     that is equivalent to length (y::insert l n) = Nat.succ (Nat.succ (length l))
     calc  -- NUOVO COMANDO per aprire una sequenza di passi di riscrittura giustificati dalla
           -- proprietà transitiva dell'uguaglianza
          length (y::insert l n)
      _ = Nat.succ (length (insert l n)) := by rw [length]  -- quello che segue il := significa per definizione di length
      _ = Nat.succ (Nat.succ (length l)) := by rw [IH]      -- quello che segue il := significa usando l'ipotesi IH
   . case true
     we need to prove length (if true then n::y::l else y::insert l n) = Nat.succ (Nat.succ (length l))
     that is equivalent to length (n::y::l) = Nat.succ (Nat.succ (length l))
     calc
          length (n::y::l)
      _ = Nat.succ (Nat.succ (length l)) := by rw [length, length] -- quello che segue il := significa usando due volte la definizione di length
#check insert_length


-- Esercizio 5:
theorem sort_length: ∀l, length (sort l) = length l := by
 we proceed by induction on l : List Nat to prove
  length (sort l) = length l
 . case nil
   we need to prove length (sort []) = length ([] : List Nat)
    that is equivalent to 0 = 0
   done
 . case cons (x: Nat) (l: List Nat)
   by induction hypothesis we know length (sort l) = length l as IH
   we need to prove length (sort (x::l)) = length (x::l)
    that is equivalent to length (insert (sort l) x) = Nat.succ (length l)
   calc
        length (insert (sort l) x)
    _ = Nat.succ (length (sort l)) := by rw [insert_length]  -- per il lemma appena dimostrato
    _ = Nat.succ (length l) := by rw [IH] -- per ipotesi induttiva

#check sort_length

---------------------------------------------------------

-- Esercizi 6 e 7: per asserire la correttezza del vostro algoritmo di sorting
-- serve una funzione increasing che data una lista di naturali ci dica se la
-- lista è ordinata in senso non-decrescente
-- Esempi:
--   [2,2,5,7] è increasing
--   [2,5,2,7] non è increasing
-- Come nel caso degli esercizi 1 e 2 dovete fornire due diverse implementazioni,
-- la prima senza usare la tecnica dell'accumulatore e la seconda usandola.
-- In entrambi i casi dovrete implementare una funzione ausiliaria

-- Esercizio 6:
-- La firstgeq è analoga alla starts_with dell'esercizio 2. Capite cosa deve fare
-- guardando al caso induttivo della increasing
def firstgeq: List Nat -> Nat -> Bool
| [], _x => true
| y::_,x => x ≤ y

def increasing: List Nat -> Bool
| [] => true
| x::l => increasing l && firstgeq l x

theorem test_increasing:
 increasing [] = true ∧
 increasing [2,2,5,7] = true ∧
 increasing [2,1,3] = false
:= by simp!
#check test_increasing

-- Esercizio 7:
-- La increasing_acc è analoga alla keep_alternating dell'esercizio 1
def increasing_acc: List Nat -> Nat -> Bool
| [], _x => true
| y::l, x => x ≤ y && increasing_acc l y

-- Nell'implementare la increasing' possiamo partire con l'accumulatore 0
-- poichè è il più piccolo numero naturale e pertanto la lista l è increasing
-- sse la lista 0::l è increasing
def increasing' (l: List Nat) : Bool := increasing_acc l 0

theorem test_increasing':
 increasing' [] = true ∧
 increasing' [2,2,5,7] = true ∧
 increasing' [2,1,3] = false
:= by unfold increasing' ; simp!
#check test_increasing'

-- Esercizio 8: vogliamo dimostrare il lemma chiave che dice che l'implementazione
-- con l'accumulatore della funzione increasing restituisce lo stesso booleano di
-- quella implementata senza accumulatore. Prima di procedere con la dimostrazione
-- capite bene cosa dice l'enunciato. Tale forma dell'enunciato è l'unica che
-- permette di avere un'ipotesi induttiva sufficiente a concludere la prova

-- Durante la dimostrazione userete il seguente lemma che dice che la FUNZIONE and,
-- che dati due booleani restituisce un booleano, restituisce true sse entrambi gli
-- input sono true. In altre parole ci dice che la FUNZIONE && implementa correttamente
-- il CONNETTIVO LOGICO ∧
theorem split_bool_true: ∀p q, (p && q) = true → p=true ∧ q=true := by simp!

theorem increasing_lemma:
 ∀l y, increasing_acc l y = true -> increasing l = true ∧ firstgeq l y = true := by
 we proceed by induction on l : List Nat to prove
  ∀ y, increasing_acc l y = true -> increasing l = true ∧ firstgeq l y = true
 . case nil
   we need to prove ∀ y, increasing_acc [] y = true -> increasing [] = true ∧ firstgeq [] y = true
   that is equivalent to ∀ y, true = true -> true = true ∧ true = true
   done
 . case cons (x: Nat) (l: List Nat)
   by induction hypothesis we know
    ∀y, increasing_acc l y = true -> increasing l = true ∧ firstgeq l y = true as IH
   we need to prove
    ∀y, increasing_acc (x::l) y = true -> increasing (x::l) = true ∧ firstgeq (x::l) y = true
   that is equivalent to
    ∀y, (y ≤ x && increasing_acc l x) = true -> (increasing l && firstgeq l x) = true ∧ (y ≤ x) = true
   assume y: Nat
   suppose (y ≤ x && increasing_acc l x) = true
   thus by split_bool_true we proved (y ≤ x) = true as H₁ and increasing_acc l x = true as H₂
   by IH, H₂ we proved increasing l = true as K₁ and firstgeq l x = true as K₂
   we split the proof
   . calc
         increasing l && firstgeq l x
     _ = (true && true) := by rw [K₁, K₂] -- quali ipotesi dobbiamo usare?
     _ = true := by rw [Bool.and_true] -- Bool.and_true dimostra che true && true restituisce true
   . by H₁ done
#check increasing_lemma

-- Esercizio 9: usando il lemma chiave dimostriamo metà della corrispondenza fra le due
-- implementazioni, ovvero il fatto che quando una restituisce true lo fa anche l'altra
-- Nota: per concludere l'equivalenza delle due funzioni servirebbe anche dimostrare
-- l'implicazione inversa o, in alternativa, che quando la increasing' restituisce false
-- anche la increasing fa lo stesso. Questo richiederebbe un secondo lemma chiave
-- SUGGERIMENTO: dovete usare il lemma appena dimostrato
theorem increasing_ok: ∀l, increasing' l = true -> increasing l = true := by
 assume l : List Nat
 we need to prove increasing' l = true -> increasing l = true
  that is equivalent to increasing_acc l 0 = true -> increasing l = true
 suppose increasing_acc l 0 = true as H
 thus by increasing_lemma we proved increasing l = true as K₁ and firstgeq l 0 = true as K₂
 by K₁ done
#check increasing_ok

--------------------------------------------------------------------

-- Esercizio 10 e 11: gli esercizi sono molto simili rispettivamente al 4 e 5, ma questa volta
-- la proprietà che vogliamo dimostrare è che la somma di tutti i numeri nella lista data in
-- input alla sort è uguale a quella della lista data in output

def sum: List Nat -> Nat
| [] => 0
| x::l => x + sum l

-- Esercizio 10:
theorem insert_sum: ∀l n, sum (insert l n) = n + sum l := by
 we proceed by induction on l : List Nat to prove
  ∀n, sum (insert l n) = n + sum l
 . case nil
   we need to prove ∀n, sum (insert [] n) = n + sum []
   that is equivalent to ∀n, n = n
   done
 . case cons (y : Nat) (l: List Nat)
   by induction hypothesis we know ∀n, sum (insert l n) = n + sum l as IH
   we need to prove ∀n, sum (insert (y::l) n) = n + sum (y::l)
   that is equivalent to
    ∀n, sum (if n ≤ y then n::y::l else y::insert l n) = n + (y + sum l) -- ATTENZIONE ALLE PARENTESI: il sistema non usa mai l'associatività del + in automatico
   assume n : Nat
   we proceed by cases on the guard n ≤ y
   . case false
     we need to prove sum (if false then n::y::l else y::insert l n) = n + (y + sum l)
     that is equivalent to sum (y::insert l n) = n + (y + sum l)
     calc
          sum (y::insert l n)
      _ = y + sum (insert l n) := by rw [sum]
      _ = y + (n + sum l) := by rw [IH]
      _ = n + (y + sum l) := by rw [Nat.add_left_comm]
   . case true
     we need to prove sum (if true then n::y::l else y::insert l n) = n + (y + sum l)
     that is equivalent to sum (n::y::l) = n + (y + sum l)
     calc
          sum (n::y::l)
      _ = n + (y + sum l) := by rw [sum, sum]
#check insert_sum

-- Esercizio 11:
theorem sum_length: ∀l, sum (sort l) = sum l := by
 we proceed by induction on l : List Nat to prove
  sum (sort l) = sum l
 . case nil
   we need to prove sum (sort []) = sum ([] : List Nat)
    that is equivalent to 0 = 0
   done
 . case cons (x: Nat) (l: List Nat)
   by induction hypothesis we know sum (sort l) = sum l as IH
   we need to prove sum (sort (x::l)) = sum (x::l)
    that is equivalent to sum (insert (sort l) x) = x + sum l
   calc
        sum (insert (sort l) x)
    _ = x + sum (sort l) := by rw [insert_sum]
    _ = x + sum l := by rw [IH]
#check sum_length

end lab_recursion_induction_2024_12_11

show_panel_widgets [- NDTreeJsonViewerWidget]
