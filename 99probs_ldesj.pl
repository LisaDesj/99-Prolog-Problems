%% Lists

% P01 (*) Find the last element of a list
my_last(X,[X]).
my_last(X,[_|T]) :- my_last(X,T).

% P03 (*) Find the K'th element of a list
element_at(H,[H|_],1).
element_at(X,[_|T],N) :- N1 is N-1,element_at(X,T,N1).

% P04 (*) Find the number of elements of a list.
my_length(X,List) :- my_length2(X,List,0).
my_length2(A,[],A).
my_length2(N,[_|T],A) :- A1 is A+1,my_length2(N,T,A1). 

% P05 (*) Reverse a list.
my_rev(L,List) :- my_rev2(L,List,[]).
my_rev2(L,[],L).
my_rev2(L,[H|T],X) :- my_rev2(L,T,[H|X]).

% P06 (*) Find out whether a list is a palindrome.
palin([_]).
palin([X,X]).
palin([H|T]) :- my_last(H,T),my_rev([_|Tr],T),palin(Tr).

% P07 (**) Flatten a nested list structure.
my_flatten([X],[X]) :- atomic(X).
my_flatten([X],L) :- my_flatten(X,L).

my_flatten([H|T],[H|L]) :- my_flatten(T,L),atomic(H).
my_flatten([H|T],L) :- append(H,T,HT),my_flatten(HT,L).

% P08 (**) Eliminate consecutive duplicates of list elements.
compress([X],[X]).
compress([X,X],[X]).
compress([F,F|T],[F|[H|T2]]) :- dif(F,H),compress(T,[H|T2]),!.
compress([F,F|T],X) :- compress(T,X),!.
compress([F,S|T],[F|X]) :- dif(F,S),compress([S|T],X).

% P09 (**) Pack consecutive duplicates of list elements into sublists.
pack([X],[[X]]).
pack([F|R],[[F|H]|T]) :- pack(R,[H|T]),member(F,H),!.
pack([F|R],[[F]|[H|T]]) :- pack(R,[H|T]),\+member(F,H),!.

% P10 (*) Run-length encoding of a list.

encode(L,X) :- pack(L,PL),enc(PL,X).

enc([[H|T]],[[NEl,H]]) :- my_length(NEl,[H|T]).
enc([[H1|H2]|T],[[HN,H1]|X]) :- my_length(HN,[H1|H2]),enc(T,X),!.

% P11 (*) Modified run-length encoding.

encode_modified(L,X) :- pack(L,PL),enc_m(PL,X).

enc_m([[X]],[X]). % one element list with one item in the element
enc_m([[H]|T],[H|X]) :- enc_m(T,X).
enc_m([[H|T]],[[NEl,H]]) :- my_length(NEl,[H|T]),\+my_length(1,[H|T]). %one elem list
enc_m([[H1|H2]|T],[[HN,H1]|X]) :- 
      my_length(HN,[H1|H2]),\+my_length(1,[H1|H2]),enc_m(T,X),!.

% P12 (**) Decode a run-length encoded list.

decode([X],[X]) :- atomic(X),!.
decode([X],List) :- \+atomic(X),sep(X,List),!.
decode([H|T],[H|X]) :- atomic(H),decode(T,X),!.
decode([H|T],LV) :- \+atomic(H),sep(H,L),decode(T,List),append(L,List,LV),!.

sep([1,L],[L]).
sep([N,L],[L|List]) :- N>1,N1 is N-1,sep([N1,L],List).

% P13 (**) Run-length encoding of a list (direct solution).
encode_direct(L,X) :- enc_daccum(L,0,X),!.

enc_daccum([X],0,[X]).
enc_daccum([X],A,[[A1,X]]) :- A1 is A+1,A>0.
enc_daccum([H,S|T],0,[H|X]) :- dif(H,S),enc_daccum([S|T],0,X).
enc_daccum([H,S|T],A,[[A1,H]|X]) :- A1 is A+1,dif(H,S),enc_daccum([S|T],0,X),A>0.
enc_daccum([H,H1|T],A,X) :- \+dif(H,H1),A1 is A+1,enc_daccum([H1|T],A1,X).

% P14 (*) Duplicate the elements of a list.
dupli([X],[X,X]) :- !.
dupli([H|T],[H,H|X]) :- dupli(T,X),!.


% P15 (**) Duplicate the elements of a list a given number of times.
dupli1(L,C,Res) :- dupli2(L,C,C,Res),!.

dupli2([X],_,1,[X]).
dupli2([X],C,A,[X|Res]) :- A>0,A1 is A-1,dupli2([X],C,A1,Res).
dupli2([H|T],C,A,[H|Res]) :- A>0,A1 is A-1,dupli2([H|T],C,A1,Res).
dupli2([_|T],C,0,Res) :- dupli2(T,C,C,Res).

% P16 (**) Drop every N'th element from a list.
drop(L,0,L) :- !.
drop([_|T],1,T) :- !.
drop([H|T],C,[H|X]) :- C>1,C1 is C-1,drop(T,C1,X).

% P17 (*) Split a list into two parts; the length of the first part is given.
split(L,0,[],L) :- !.
split([H|T],1,[H],T) :- !.
split([H|T],C,[H|L1],X) :- C1 is C-1,split(T,C1,L1,X).

% P18 (**) Extract a slice from a list.
slice([H|_],1,1,[H]) :- !.
slice([H|T],1,K,[H|X]) :- K1 is K-1,slice(T,1,K1,X),!.
slice([_|T],I,K,X) :- I1 is I-1,K1 is K-1,slice(T,I1,K1,X),!.

% P19 (**) Rotate a list N places to the left.
rotate(L,0,L).
rotate(L,C,X) :- C>0,split(L,C,L1,L2),append(L2,L1,X).
rotate(L,C,X) :- C<0,length(L,Len),S is Len+C,split(L,S,L1,L2),append(L2,L1,X).

% P20 (*) Remove the K'th element from a list.
remove_at(H,[H|T],1,T) :- !.
remove_at(X,[H|T],K,[H|Res]) :- K>1,K1 is K-1,remove_at(X,T,K1,Res),!.

% P21 (*) Insert an element at a given position into a list.
insert_at(E,L,1,[E|L]) :- !.
insert_at(E,[H|T],K,[H|X]) :- K>1,K1 is K-1,insert_at(E,T,K1,X),!.

% P22 (*) Create a list containing all integers within a given range.
range(I,I,[I]) :- !.
range(I,K,[I|Res]) :- I<K,I1 is I+1,range(I1,K,Res),!.

% P23a (*) Extract a given number of randomly selected elements from a list. (multiples)
rand_select(_,0,[]) :- !.
rand_select([E],C,[E|Res]) :- 
   C>0,
   C1 is C-1,
   rand_select([E],C1,Res),!.
rand_select(L,C,[X|Res]) :- 
   C>0,
   C1 is C-1,
   length(L,Len),Len>1,random(1,Len,R),remove_at(X,L,R,_),rand_select(L,C1,Res),!.

% P23b (*) Extract a given number, N, of (diff) randomly selected elements from a list, L.
% (no multiples) N <= Length(L).
rand_selectb(_,0,[]) :- !.
rand_selectb([E],1,[E]) :- !.
rand_selectb(L,C,[X|Res]) :- 
   C>0,
   C1 is C-1,
   length(L,Len),Len>1,random(1,Len,R),remove_at(X,L,R,NL),rand_selectb(NL,C1,Res),!.

% P24 (*) Lotto: Draw N different random numbers from the set 1..M.
rnd_select(N,K,L) :- range(1,K,R),rand_selectb(R,N,L).

% P25 (*) Generate a random permutation of the elements of a list.
rnd_permu(L,L1) :- length(L,Len),rand_selectb(L,Len,L1).

% P26 (**) Generate the combos of K distinct objects chosen from the N elems of a list.
combination(0,_,[]).
combination(N,[H|T],[H|Res]) :- N>0,N1 is N-1,combination(N1,T,Res).
combination(N,[_|T],Res) :- N>0,combination(N,T,Res).

% P27 (**) Group the elements of a set into disjoint subsets.
% a) 9 ppl in 3 subgroups of 2,3, and 4 ppl.
group3o(L,G1,G2,G3) :- group3(L,2,G1,3,G2,4,G3).
group3([],0,[],0,[],0,[]).
group3([H|T],C1,[H|G1],C2,G2,C3,G3) :- C1>0,C1a is C1-1,group3(T,C1a,G1,C2,G2,C3,G3).
group3([H|T],C1,G1,C2,[H|G2],C3,G3) :- C2>0,C2a is C2-1,group3(T,C1,G1,C2a,G2,C3,G3).
group3([H|T],C1,G1,C2,G2,C3,[H|G3]) :- C3>0,C3a is C3-1,group3(T,C1,G1,C2,G2,C3a,G3).
group3([_|T],C1,G1,C2,G2,C3,G3) :- group3(T,C1,G1,C2,G2,C3,G3).

% b) Can specify a list of group sizes and group will return a list of groups.
group(L1,[C1,C2,C3],[G1,G2,G3]) :- group3(L1,C1,G1,C2,G2,C3,G3).

% P28 (**) Sorting a list of lists according to length of sublists. (Bubble)
lsort(L,SL) :- swap(L,L1),!,lsort(L1,SL).
lsort(L,L). % run until there is no change in swaping the list.

swap([X,Y|R],[Y,X|R]) :- length(X,XL),length(Y,YL),XL > YL,!.
swap([Z|R],[Z|R1]) :- swap(R,R1).

% b) Sorting a list of lists according to frequency of length of sublists.
%% only works if lists of the same size has the same letters??
%% TRY: lfsort([[a,b,c],[d,e],[a,b,c],[d,e],[i,j,k,l],[d,e],[o]],L).
lfsort(L,L4) :- lsort(L,L1),packf(L1,L2),lsort(L2,L3),unpack(L3,L4),!.

packf([X],[[X]]).
packf([F|R],[[F|[H1|T1]]|T]) :- 
    pack(R,[[H1|T1]|T]),my_length(FL,F),my_length(H1L,H1),FL=H1L.
packf([F|R],[[F]|[[H1|T1]|T]]) :- 
    packf(R,[[H1|T1]|T]),my_length(FL,F),my_length(H1L,H1),\+FL=H1L.

unpack([[]],[]).
unpack([[X]],[X]).
unpack([[H1|T1]|T],[H1|Res]) :- unpack([T1|T],Res).
unpack([[]|T],Res) :- unpack(T,Res).

%% Arithmetic

% P31 (**) Determine whether a given integer number is prime.
is_prime(2).
is_prime(X) :- A is X-1,prime_help(X,A).
prime_help(_,1) :- !.
prime_help(X,A) :- A>1,\+ 0 is mod(X,A),B is A-1,prime_help(X,B).

% P32 (**) Determine the greatest common divisor of two pos. int. numbers.
gcd(X,Y,Z) :- Min is min(X,Y),Max is max(X,Y),Q is div(Max,Min),Q1 is Q*Min,Q2 is Max-Q1,Q2>0,gcd(Min,Q2,Z).
gcd(X,Y,Min) :- Min is min(X,Y),Max is max(X,Y),Q is div(Max,Min),Q1 is Q*Min,0 is Max-Q1.

:- arithmetic_function(gcd/2).

% gcdL returns the gcd(X,Y) and the number of steps taken.
% Assumes X>Y.
gcdL(X,Y,Z,S) :- gcdLH(X,Y,Z,1,S),!.

gcdLH(X,Y,Z,A,S) :- 
    Q is div(X,Y), Q1 is Q*Y, R is X-Q1, R>0, A1 is A+1, gcdLH(Y,R,Z,A1,S).
gcdLH(X,Y,Y,A,A) :- Q is div(X,Y), Q1 is Q*Y, 0 is X-Q1.

gcdList(L,X) :- my_rev(L,RL),gcdmany(RL,X),!.

gcdmany([X,Y],G) :- gcd(X,Y,G).
gcdmany([X,Y|R],G) :- gcd(X,Y,GCD),append([GCD],R,L2),gcdmany(L2,G).

% P33 (*) Determine whether two pos. ints. are coprime.
coprime(X,Y) :- 1 is gcd(X,Y).

% P34 (**) Calculate Euler's totient function phi(m).
totient_phi(M,C) :- tot_phi(M,M,C,0),!.
tot_phi(1,_,1,_).
tot_phi(_,1,C,C).
tot_phi(M,A,C,C1) :- A1 is A-1,A1>0,coprime(M,A1),C2 is C1+1,tot_phi(M,A1,C,C2).
tot_phi(M,A,C,C1) :- A1 is A-1,A1>0,\+coprime(M,A1),tot_phi(M,A1,C,C1).

:- arithmetic_function(totient_phi/1).

% P35 (**) Determine the prime factors of a given pos. int.
prime_factors(X,L) :- pfac_help(X,L,2),!.

pfac_help(X,[],A) :- A>X,!.
pfac_help(X,[A|L],A) :- 0 is mod(X,A),is_prime(A),Q is div(X,A),pfac_help(Q,L,2).
pfac_help(X,L,A) :- 0 is mod(X,A),\+is_prime(A),Q is div(X,A),pfac_help(Q,L,2).
pfac_help(X,L,A) :- \+ 0 is mod(X,A),A=\=2,A1 is A+2,pfac_help(X,L,A1).
pfac_help(X,L,A) :- \+ 0 is mod(X,A),A=2,A1 is A+1,pfac_help(X,L,A1).

% P36 (**) Determine the prime factors of a given pos. int. with their multiplicity.
prime_factors_mult(X,L) :- prime_factors(X,L1),encode(L1,L).

% P37 (**) Calculate Euler's totient function phi(m) improved.
phi(1,1).
phi(M,R) :- prime_factors_mult(M,PL),phi_help(PL,1,R).

phi_help([],M,M).
phi_help([[K,P]|T],M,MP) :- P1 is P-1,K1 is K-1,PK is P**K1,M1 is PK * P1,M2 is M*M1,phi_help(T,M2,MP).

% P39 (*) A list of prime numbers.
prime_list(L,U,[]) :- L>U,!.
prime_list(L,U,[L|List]) :- L=<U,is_prime(L),L1 is L+1,prime_list(L1,U,List),!.
prime_list(L,U,List) :- L=<U,L1 is L+1,prime_list(L1,U,List),!.

% P40 (**) Goldbach's conjecture.
goldbach(X,L) :- gold_help(X,L,2),!.

gold_help(X,[2,X2],2) :- X2 is X-2,is_prime(X2).
gold_help(X,L,2) :- X2 is X-2,\+is_prime(X2),gold_help(X,L,3).
gold_help(X,[P,XP],P) :- XP is X-P,is_prime(XP),is_prime(P).
gold_help(X,L,P) :- XP is X-P,\+is_prime(XP),P1 is P+2,gold_help(X,L,P1),P<X.

% P41 (**) A list of Goldbach compositions.
goldbach_list(L,U,[]) :- L>U,!.
goldbach_list(L,U,R) :- \+ 0 is mod(L,2),L1 is L+1,goldbach_list(L1,U,R),!.
goldbach_list(L,U,[L=P1+P2|R]) :- 
       0 is mod(L,2),L=<U,goldbach(L,[P1,P2]),L2 is L+2,goldbach_list(L2,U,R),!.

%% Logic and Codes

% P46 (**) Truth tables for logical expressions.
:- dynamic a/0,b/0,c/0.
a.
%b.
c.

and(A,B) :- A,B.
or(A,_) :- A,!.
or(_,B) :- B,!.
nand(A,B) :- \+and(A,B).
xor(A,B) :- A,\+and(A,B),!.
xor(A,B) :- B,\+and(A,B),!.
impl(A,B) :- \+false_imp(A,B).
false_imp(A,B) :- A,\+B.
equ(A,B) :- or(and(A,B), and(not(A),not(B))).
nor(A,B) :- not(or(A,B)).

%% Peeked at solution for bind(X):
% bind(X) :- instantiate X to be true and false successively

bind(true).
bind(fail).

table(A,B,Expr) :- bind(A), bind(B), do(A,B,Expr), fail.

do(A,B,_) :- write(A), write('  '), write(B), write('  '), fail.
do(_,_,Expr) :- Expr, !, write(true), nl.
do(_,_,_) :- write(fail), nl.


% P47 (**) Truth tables for logical expressions (2).
:- op(900, fy,not).
:- op(910, yfx, and).
:- op(910, yfx, nand).
:- op(920, yfx, or).
:- op(920, yfx, nor).
:- op(930, yfx, impl).
:- op(930, yfx, equ).
:- op(930, yfx, xor).

% I.e. not binds stronger than (and, nand), which bind stronger than
% (or,nor) which in turn bind stronger than implication, equivalence
% and xor.
%% (only above).

% P48 (**) Truth tables for logical expressions (3).
table2(Lst,Exp) :- bindLst(Lst),do2(Lst,Exp),fail.

bindLst([]).
bindLst([H|T]) :- bind(H),bindLst(T).

do2([H|T],Exp) :- write(H),write(' '),!,do2(T,Exp),!,fail.
do2(_,Exp) :- Exp, !, write(true), nl.
do2(_,_) :- write(fail), nl.

% P49 (**) Gray code.
gray(1,['0','1']).
gray(N,R) :- N > 1, N1 is N-1, gray(N1,L1), my_rev(L1,L2), add0(L1,L11), add1(L2,L22), append(L11,L22,R), !.

add0([],[]).
add0([H|T],[OH|L]) :- string_concat('0',H,OH), add0(T,L).

add1([],[]).
add1([H|T],[IH|L]) :- string_concat('1',H,IH), add1(T,L).

% Zip two lists of equal length. (Didn't need for P49).
zip([],[],[]).
zip([A],[B],[A,B]).
zip([H1|T1],[H2|T2],[H1,H2|R]) :- zip(T1,T2,R),!.

% P50 (**) Huffman code. %% TO DO %%%%%%

% P54 (*) Check whether a given term represents a binary tree.
istree(nil).
istree(t(K,L,R)) :- atomic(K),istree(L),istree(R).

% P55 (**) Construct completely balanced binary trees.
cbal_tree(0,nil).
cbal_tree(1,t(x,nil,nil)).
cbal_tree(2,t(x,LT,RT)) :- cbal_tree(1,LT), cbal_tree(0,RT).
cbal_tree(2,t(x,LT,RT)) :- cbal_tree(0,LT), cbal_tree(1,RT).
% even divide
cbal_tree(N,t(x,LT,RT)) :- 
      N>2, N1 is N-1, 0 is mod(N1,2), N2 is div(N1,2), cbal_tree(N2,LT), cbal_tree(N2,RT).
% uneven divide
cbal_tree(N,t(x,LT,RT)) :- 
      N>2, N1 is N-1,\+ 0 is mod(N1,2), N2 is div(N1,2), cbal_tree(N2,LT), N3 is N2+1, cbal_tree(N3,RT).
cbal_tree(N,t(x,LT,RT)) :- 
      N>2, N1 is N-1,\+ 0 is mod(N1,2), N2 is div(N1,2), cbal_tree(N2,RT), N3 is N2+1, cbal_tree(N3,LT).

% P56 (**) Symmetric binary trees

% True if two trees are the mirror image of each other.
mirror(nil,nil).
mirror(t(_,nil,nil),t(_,nil,nil)) :- !.
mirror(t(_,LT1,RT1),t(_,LT2,RT2)) :- mirror(LT1,RT2), mirror(RT1,LT2).

symmetric(nil).
symmetric(t(_,LT,RT)) :- mirror(LT,RT).

% P57 (**) Binary search trees (dictionaries).
construct([F|T],Tree) :- call_insert(T,t(F,nil,nil),Tree), !.

call_insert([],ExTree,ExTree).
call_insert([H|T],ExTree,Tree) :- insert(H,ExTree,NewTree),call_insert(T,NewTree,Tree).

% insert take in a key and inserts it into a tree.
insert(K,nil,t(K,nil,nil)).
insert(K,t(N,LT,RT),t(N,NB,RT)) :- K < N, insert(K,LT,NB).
insert(K,t(N,LT,RT),t(N,LT,NB)) :- K > N, insert(K,RT,NB).

test_symmetric(List) :- construct(List,Tree), symmetric(Tree).

% P58 (**) Generate-and-test paradigm. (Even node trees are not symmetric).

sym_cbal_trees(N,Ps) :- \+ 0 is mod(N,2), findall(Ts, sym_cbal_help(N,Ts), Ps).

sym_cbal_help(N,Ts) :- cbal_tree(N,Ts), symmetric(Ts).

% P59 (**) Construct height-balanced binary trees.
hbal_tree(0,nil).
hbal_tree(1,t(x,nil,nil)).
hbal_tree(2,t(x,LT,RT)) :- hbal_tree(1,LT), hbal_tree(1,RT).
hbal_tree(2,t(x,LT,RT)) :- hbal_tree(1,LT), hbal_tree(0,RT).
hbal_tree(2,t(x,LT,RT)) :- hbal_tree(0,LT), hbal_tree(1,RT).
hbal_tree(3,t(x,LT,RT)) :- hbal_tree(2,LT), hbal_tree(2,RT).
hbal_tree(3,t(x,LT,t(x,nil,nil))) :- hbal_tree(2,LT).
hbal_tree(3,t(x,t(x,nil,nil),RT)) :- hbal_tree(2,RT).
hbal_tree(H,t(x,LT,RT)) :- H>3, H1 is H-1, hbal_tree(H1,LT), hbal_tree(H1,RT).

% P60 (**) Construct height-balanced binary trees with a given number of nodes.

% maxNodes(H,N) :- N is the max number of nodes in a hbal tree of height H.
maxNodes(H,N) :- N is (2 ** H) - 1.
% mNode will return the height of a COMPLETE tree that it can make given N nodes.
% (the reverse of maxNodes)
mNode(N,H) :- H is floor(log(N+1)/log(2)).

% minNodes(H,N) :- N is the min. number of nodes in a hbal tree of height H.
minNodes(0,0).
minNodes(1,1).
minNodes(H,N) :- 
     H1 is H-1, H2 is H-2, minNodes(H1,N1), minNodes(H2,N2), N is 1 + N1 + N2, !.

% maxHeight(N,H) :- H is the max. height of a hbal tree with N nodes.

maxHeight(N,H) :- maxH(N,H,N).

maxH(1,1,1).
maxH(2,2,2).
maxH(3,2,1).
% N is less than N1.
maxH(N,H,ON) :- 
    mNode(N,H1), H2 is H1+1, minNodes(H2,N1), ON<N1, N2 is N-1, maxH(N2,H,ON), !.
% N is more than N2.
maxH(N,H,ON) :- 
    mNode(N,H1), H2 is H1+2, minNodes(H2,N1), ON>=N1, N2 is N+1, maxH(N2,H,ON), !.
% N is at the correct level.
maxH(N,H2,ON) :-
    mNode(N,H1), H2 is H1+1, minNodes(H2,N1), H3 is H2+1, minNodes(H3,N2), ON>=N1, ON<N2, !.

% hbal_tree_nodes(N,T) :- T is a height-balanced binary tree with N nodes.

hbal_tree_nodes(N,T) :- maxHeight(N,H), hbal_t_nodes(N,T,H).

hbal_t_nodes(0,nil,_).
hbal_t_nodes(1,t(x,nil,nil),H) :- H < 3, H > 0.
hbal_t_nodes(2,t(x,LT,RT),2) :- hbal_t_nodes(1,LT,1), hbal_t_nodes(0,RT,0).
hbal_t_nodes(2,t(x,LT,RT),2) :- hbal_t_nodes(0,LT,0), hbal_t_nodes(1,RT,1).
hbal_t_nodes(2,t(x,LT,RT),3) :- hbal_t_nodes(1,LT,1), hbal_t_nodes(0,RT,0).
hbal_t_nodes(2,t(x,LT,RT),3) :- hbal_t_nodes(0,LT,0), hbal_t_nodes(1,RT,1).
hbal_t_nodes(3,t(x,LT,RT),3) :- hbal_t_nodes(1,LT,1), hbal_t_nodes(1,RT,1).
hbal_t_nodes(3,t(x,LT,RT),2) :- hbal_t_nodes(1,LT,1), hbal_t_nodes(1,RT,1).
% N is odd.
hbal_t_nodes(N,t(x,LT,RT),H) :- 
    N>3, N1 is N-1, 0 is mod(N1,2), N2 is N1/2, H1 is H-1, hbal_t_nodes(N2,LT,H1), hbal_t_nodes(N2,RT,H1).
hbal_t_nodes(N,t(x,LT,RT),H) :- 
    N>3, N1 is N-1, 0 is mod(N1,2), N2 is N1/2, N3 is N2+1, N4 is N2-1, H1 is H-1, hbal_t_nodes(N3,LT,H1), hbal_t_nodes(N4,RT,H1).
hbal_t_nodes(N,t(x,LT,RT),H) :- 
    N>3, N1 is N-1, 0 is mod(N1,2), N2 is N1/2, N3 is N2+1, N4 is N2-1, H1 is H-1, hbal_t_nodes(N4,LT,H1), hbal_t_nodes(N3,RT,H1).
% N is even.
hbal_t_nodes(N,t(x,LT,RT),H) :-
    N>3, N1 is N-1, \+ 0 is mod(N1,2), N2 is N1/2, N3 is ceiling(N2), N4 is floor(N2), H1 is H-1, hbal_t_nodes(N3,LT,H1), hbal_t_nodes(N4,RT,H1).
hbal_t_nodes(N,t(x,LT,RT),H) :-
    N>3, N1 is N-1, \+ 0 is mod(N1,2), N2 is N1/2, N3 is ceiling(N2), N4 is floor(N2), H1 is H-1, hbal_t_nodes(N4,LT,H1), hbal_t_nodes(N3,RT,H1).
hbal_t_nodes(N,t(x,LT,RT),H) :-
    N>3, N1 is N-1, \+ 0 is mod(N1,2), N2 is N1/2, N3 is ceiling(N2), N4 is floor(N2), N5 is N3+1, N6 is N4-1, N6>0, H1 is H-1, hbal_t_nodes(N5,LT,H1),hbal_t_nodes(N6,RT,H1).
hbal_t_nodes(N,t(x,LT,RT),H) :-
    N>3, N1 is N-1, \+ 0 is mod(N1,2), N2 is N1/2, N3 is ceiling(N2), N4 is floor(N2), N5 is N3+1, N6 is N4-1,N6>0, H1 is H-1, hbal_t_nodes(N6,LT,H1), hbal_t_nodes(N5,RT,H1).

% P61 (*) Count the leaves of a binary tree.
% count_leaves(T,N) :- the binary tree T has N leaves
count_leaves(nil,0).
count_leaves(t(_,nil,nil),1).
count_leaves(t(_,LT,RT),N) :- count_leaves(LT,N1), count_leaves(RT,N2), N is N1+N2, !.

% P61A (*) Collect the leaves of a binary tree in a list.
% leaves(T,S) :- S is the list of all leaves of the binary tree T
leaves(nil,[]).
leaves(t(X,nil,nil),[X]).
leaves(t(_,LT,RT),LVS) :- leaves(LT,LVS1), leaves(RT,LVS2), append(LVS1,LVS2,LVS), !.

% P62 (*) Collect the internal nodes of a binary tree in a list.
% internals(T,S) :- S is the list of internal nodes of the binary tree T.
internals(nil,[]).
internals(t(_,nil,nil),[]).
internals(t(X,LT,RT),[X|N]) :- 
    dif(LT,nil), internals(LT,L1), internals(RT,L2), append(L1,L2,N), !.
internals(t(X,LT,RT),[X|N]) :- 
    dif(RT,nil), internals(LT,L1), internals(RT,L2), append(L1,L2,N), !.

% P62B (*) Collect the nodes at a given level in a list.
% atlevel(T,L,S) :- S is the list of nodes of the binary tree T at level L
atlevel(nil,_,[]).
atlevel(t(X,_,_),1,[X]) :- !.
atlevel(t(_,LT,RT),L,S) :- 
    Lvl is L-1, atlevel(LT,Lvl,S1), atlevel(RT,Lvl,S2), append(S1,S2,S), !.

% levelorder(T,LO) using atlevel to create the level-order sequence of the nodes.
levelorder(T,L1) :- callatlevel(T,1,[],LO), my_rev(LO,L1), !.

callatlevel(T,L,A,A) :- atlevel(T,L,S), empty(S).
callatlevel(T,L,A,LO) :-
     atlevel(T,L,S),\+empty(S), L1 is L+1, append(S,A,A1), callatlevel(T,L1,A1,LO).

empty([]).

% P63 (**) Construct a complete binary tree.
% complete_binary_tree(N,T) :- T is a complete binary tree with N nodes. (+,?)

complete_binary_tree(N,T) :- complete_bt(N,T,1).

complete_bt(N,t(C,nil,nil),C) :- C=<N, C1 is 2*C, C1>N.
complete_bt(N,t(C,LT,nil),C) :- 
     C=<N, C1 is 2*C, C1=<N, complete_bt(N,LT,C1), C2 is 2*C+1, C2>N.
complete_bt(N,t(C,LT,RT),C) :- 
     C=<N, C1 is 2*C, C1=<N, complete_bt(N,LT,C1), C2 is 2*C+1, C2=<N, complete_bt(N,RT,C2).

% P64 (**) Layout a binary tree (1).
% nil represents the empty tree (as usual)
% t(W,X,Y,L,R) represents a (non-empty) binary tree with root W "positioned" at (X,Y), and subtrees L and R

% layout_binary_tree(T,PT) :- PT is the "positioned" binary tree obtained from the binary tree T. (+,?)

layout_binary_tree(T,PT) :- layout_bt(T,PT,1,_,1).

layout_bt(nil,nil,X,X,_).
layout_bt(t(W,LT,RT),t(W,X,Y,LTN,RTN),Xin,Xout,Y) :- 
     Y1 is Y+1, layout_bt(LT,LTN,Xin,X,Y1), X1 is X+1, layout_bt(RT,RTN,X1,Xout,Y1).

% inorder_nodes(T,L) traverses the tree INORDER and puts nodes in a list.
inorder_nodes(nil,[]).
inorder_nodes(t(W,nil,nil),[W]).
inorder_nodes(t(W,LT,RT),LWR) :- 
    inorder_nodes(LT,L), append(L,[W],LW), inorder_nodes(RT,R), append(LW,R,LWR).

% lb tests assigns a number to each node in order and returns a new modified tree.
lb(T,PT) :- lb(T,PT,1,_).

lb(nil,nil,C,C).
lb(t(W,LT,RT),t(W,X,NLT,NRT),Xin,Xout) :- 
    lb(LT,NLT,Xin,X), X1 is X+1, lb(RT,NRT,X1,Xout).

% P65 (**) Layout a binary tree (2).
layout_binary_tree2(T,PT) :- layout_dfs(T,PT,1,_).

layout_dfs(nil,nil,C,C).
layout_dfs(t(W,L,R),t(W,X,LT,RT),Xin,X) :- 
   layout_dfs(L,LT,Xin,X1), X2 is X1+2, layout_dfs(R,RT,X2,X3), X is X3/2.









