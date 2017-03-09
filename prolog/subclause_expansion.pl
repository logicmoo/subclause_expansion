/* Part of LogicMOO Base bb_env
% Provides a prolog database *env*
% ===================================================================
% File 'clause_expansion.pl'
% Purpose: An Implementation in SWI-Prolog of certain debugging tools
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'clause_expansion.pl' 1.0.0
% Revision: $Revision: 1.1 $
% Revised At:  $Date: 2016/07/11 21:57:28 $
% Licience: LGPL
% ===================================================================
*/
% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/util/clause_expansion.pl
:- module(subclause_expansion, [save_pred_to/2]).

/** <module> Prolog compile-time and runtime source-code transformations

 This module specifies a set of more specialized term and goal expansions

as they are read from a file before they are processed by the compiler.

The toplevel is expand_clause/2.  This uses other translators:

	* Conditional compilation
	* clause_expansion/2 rules provided by the user

Note that this ordering implies  that conditional compilation directives
cannot be generated  by  clause_expansion/2   rules:  they  must literally
appear in the source-code.

*/



:- dynamic(user:buffer_clauses/5).
:- volatile(user:buffer_clauses/5).

mst(G):- catch((G*->true;writeln(failed_mst(G))),_E,writeln(err(G))).

call_pred_to(Where,List):-is_list(List),!,maplist(call_pred_to(Where),List).
call_pred_to(Where,F/A):- call_pred_to(Where,_:F/A).
call_pred_to(Where,M:F/A):- ground(F/A),functor(P,F,A),call_pred_to(Where,M:P).
call_pred_to(Where,M:F/A):- forall(current_predicate(F/A),((functor(P,F,A),call_pred_to(Where,M:P)))).
call_pred_to(Where,M:P):-var(M),!,forall(current_module(M),call_pred_to(Where,M:P)).
call_pred_to(Where,M:P):-!,call(Where,M,P).
call_pred_to(Where,P):-forall(current_module(M),call_pred_to(Where,M:P)).


save_pred_to(Where,Each):-
  call_pred_to(save_pred_to_Act(Where),Each).

save_pred_to_Act(Where,M,P):-
  forall(clause(M:P,_,Ref), 
    (user:buffer_clauses(Where,M,_,_,Ref)-> true;
     ( ((clause(H,B,Ref), (clause_property(Ref,module(_))->true;throw( clause(H,B,Ref))),
    ignore(((clause_property(Ref,module(M)),assert(user:buffer_clauses(Where,M,H,B,Ref)),true)))))))).

erase_except(Where,Each):-
  call_pred_to(erase_except_Act(Where),Each).

erase_except_Act(Where,M,P):-
    forall(clause(M:P,_,Ref), 
    ((clause(HH,BB,Ref), 
     (clause_property(Ref,module(_))->true;throw( clause(HH,BB,Ref))),
     ignore(((clause_property(Ref,module(M)),\+ (user:buffer_clauses(Where,M,HH,BB,Ref)),
              % writeln(erase(HH,BB,Ref)),
              set_prolog_flag(access_level,system),
              catch(M:erase(Ref),_E,mst(M:retract((HH:-BB)))))))))).

restore_preds(Where):-
 forall(user:buffer_clauses(Where,M,H,B,Ref),
    (M:clause(H,B,Ref)->true; M:assert(H,B))).
 

erase_preds(Where):-
 forall(user:buffer_clauses(Where,M,H,B,Ref),
    (M:clause(H,B,Ref)->erase(Ref);true)).
 


:- save_pred_to(load_expansion,[term_expansion/2,term_expansion/4,goal_expansion/2,goal_expansion/4]).


% :- listing(user:buffer_clauses/5).

:- if( \+ current_predicate(system:each_call_cleanup/3)).
:- use_module(system:library(each_call_cleanup)).
:- endif.

:- set_module(class(library)).

:- multifile((system:clause_expansion/2,
              system:directive_expansion/2,
              system:file_body_expansion/3)).
:- dynamic((  system:clause_expansion/2,
              system:directive_expansion/2,
              system:file_body_expansion/3)).

:- multifile((clause_expansion/2,
              directive_expansion/2,
              file_body_expansion/3)).


:- meta_predicate without_subclause_expansion(0).

without_subclause_expansion(Goal):- current_prolog_flag(subclause_expansion,false),!,call(Goal).
without_subclause_expansion(Goal):- locally(set_prolog_flag(subclause_expansion,false),Goal).

:- multifile(system:goal_expansion/4).
:- dynamic(system:goal_expansion/4).
:- multifile(system:term_expansion/4).
:- dynamic(system:term_expansion/4).


:- initialization(nb_setval( '$term_position',[]),restore).
:- initialization(nb_setval( '$term',[]),restore).
:- initialization(nb_setval( '$term_e',[]),restore).


% subclause_term_expansion(When,In,Pos,Out) :- var(Pos),!, When:nonfile_term_expansion(In,Out).

subclause_term_expansion(_,_,_,_):- current_prolog_flag(subclause_expansion,false),!,false.
subclause_term_expansion(user,In,_,_):- nb_setval('$term_e',In),fail.
subclause_term_expansion(When,In,Pos,Out):- nonvar(Pos),nonvar(In),
  nb_current('$term',FileTerm),
  file_expansion(When,FileTerm,In,FileTermOut),!, In\=@=FileTermOut,
  \+ current_prolog_flag(xref,true),
  Out=FileTermOut,
  b_setval('$term',FileTermOut).

file_expansion(When,Term,(:- DirIn),(:- DirOut)):-
   (Term == (:- DirIn)) -> When:directive_expansion(DirIn,DirOut),!.

file_expansion(When,Term,In,Out):- 
   Term == In ->          When:clause_expansion(In,Out),!.

file_expansion(When,Term,(Head:-In),(Head:-Out)):-
   Term == (Head:-In) ->  When:file_body_expansion(Head,In,Out),!.


system:term_expansion(In,Pos,Out,Pos):- subclause_term_expansion(system,In,Pos,Out).

system:file_body_expansion(Head,I,_):- current_prolog_flag(show_expanders,true),dmsg(system:file_body_expansion(Head:-I)),fail.
system:clause_expansion(I,_):- current_prolog_flag(show_expanders,true),dmsg(system:clause_expansion(I)),fail.
system:directive_expansion(I,_):-  current_prolog_flag(show_expanders,true),dmsg(system:directive_expansion(I)),fail.

term_expansion(In,Pos,Out,Pos):- subclause_term_expansion(user,In,Pos,Out).

file_body_expansion(Head,I,_):- current_prolog_flag(show_expanders,true),dmsg(file_body_expansion(Head:-I)),fail.
clause_expansion(I,_):- current_prolog_flag(show_expanders,true),dmsg(clause_expansion(I)),fail.
directive_expansion(I,_):-  current_prolog_flag(show_expanders,true),dmsg(directive_expansion(I)),fail.

:- fixup_exports.

% :- set_prolog_flag(show_expanders,true).

