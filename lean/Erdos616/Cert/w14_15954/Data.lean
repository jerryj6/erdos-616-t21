import Erdos616Checkers.LratChunk
open Std.Sat
namespace E616C.w14_15954
/-- DIMACS text of the certificate CNF (embedded verbatim). -/
def cnfText : String := include_str "../../../../data/cnf/w14_15954.cnf"
def lemText0 : String := include_str "../../../../data/chunks/w14_15954/lem_0.cnf"
def lemText1 : String := include_str "../../../../data/chunks/w14_15954/lem_1.cnf"
def lemText2 : String := include_str "../../../../data/chunks/w14_15954/lem_2.cnf"
def lemText3 : String := include_str "../../../../data/chunks/w14_15954/lem_3.cnf"
def lemText4 : String := include_str "../../../../data/chunks/w14_15954/lem_4.cnf"
def lemText5 : String := include_str "../../../../data/chunks/w14_15954/lem_5.cnf"
def lemText6 : String := include_str "../../../../data/chunks/w14_15954/lem_6.cnf"
def lemText7 : String := include_str "../../../../data/chunks/w14_15954/lem_7.cnf"
def lemText8 : String := include_str "../../../../data/chunks/w14_15954/lem_8.cnf"
def lemText9 : String := include_str "../../../../data/chunks/w14_15954/lem_9.cnf"
def lemText10 : String := include_str "../../../../data/chunks/w14_15954/lem_10.cnf"
def lemTexts : Array String := #[lemText0, lemText1, lemText2, lemText3, lemText4, lemText5, lemText6, lemText7, lemText8, lemText9, lemText10]
/-- the CNF of the theorem -/
def F : CNF Nat := LratChunk.parseDimacsFast cnfText
/-- lemma blocks (untrusted data: each is re-verified as RUP) -/
def L (j : Nat) : CNF Nat := LratChunk.parseDimacsFast (lemTexts.getD j "")
end E616C.w14_15954
