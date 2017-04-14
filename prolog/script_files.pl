/* Part of LogicMOO Base bb_env
% Provides a prolog database *env*
% ===================================================================
% File 'script_files.pl'
% Purpose: An Implementation in SWI-Prolog of certain debugging tools
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'script_files.pl' 1.0.0
% Revision: $Revision: 1.1 $
% Revised At:  $Date: 2016/07/11 21:57:28 $
% Licience: LGPL
% ===================================================================
*/
% File:  $PACKDIR/subclause_expansion/prolog/script_files.pl
:- module(script_files, [
          process_this_script/0,
          process_this_stream/1,
          visit_script_term/3]).

/** <module> script_files

 Prolog source-code will echo while running

*/

% :- meta_predicate(process_this_script()).
% :- meta_predicate(process_this_stream(+)).
:- meta_predicate(visit_script_term(+,*,+)).
:- meta_predicate(in_space_cmt(0)).

:- module_transparent(process_this_script/0).
:- module_transparent(process_this_stream/1).
:- module_transparent(visit_script_term/3).
:- module_transparent(in_space_cmt/1).

consume_stream(In) :-
        repeat,
            (   at_end_of_stream(In)
            ->  !
            ;   read_pending_codes(In, _Chars, []),
                fail
            ).

%% process_this_script is det.
%
% Process This Script.
%
process_this_script:- current_prolog_flag(xref,true),!.
process_this_script:- 
  prolog_load_context(stream,S), !, 
  repeat,
  once(process_this_stream(S)),
  at_end_of_stream(S).

in_space_cmt(Goal):- call_cleanup(prepend_each_line(' % ',Goal),format('~N',[])),flush_output.

:- thread_local(t_l:block_comment/0).

till_eol(S):- read_line_to_string(S,String),format('~N~s~n',[String]),flush_output.

%% process_this_stream( ?S) is det.
%
% Process file stream input
%
process_this_stream(S):- at_end_of_stream(S),!,flush_output.
process_this_stream(S):- peek_code(S,W),char_type(W,end_of_line),!,get_code(S,W),put(W).
process_this_stream(S):- t_l:block_comment,peek_string(S,2,W),W="*/",retractall(t_l:block_comment),!,till_eol(S).
process_this_stream(S):- t_l:block_comment,!,till_eol(S).
process_this_stream(S):- peek_string(S,2,W),W="/*",asserta(t_l:block_comment),!,till_eol(S).
process_this_stream(S):- peek_string(S,2,W),W=" %",!,read_line_to_string(S,_).
process_this_stream(S):- peek_string(S,1,W),W="%",!,till_eol(S).
process_this_stream(S):- peek_code(S,W),char_type(W,white),\+ char_type(W,end_of_line),get_code(S,W),put(W),!.
process_this_stream(S):- must((read_term(S,T,[variable_names(Vs)]),put_variable_names( Vs))),
  call(b_setval,'$variable_names',Vs),
  must((format('~N~n',[]),flush_output,portray_one_line(T),format('~N~n',[]))),!,flush_output,
  prolog_load_context(term_position,Pos),must(visit_script_term(Pos,T,Vs)),!,
  format('~N',[]),!.


%% visit_script_term(+Pos, +Term, +Vs) is det.
%
% Process A Script Term.
%
visit_script_term(Pos,   T,      Vs):- fail,dmsg(visit_script_term(Pos,T,Vs)),fail.
visit_script_term( _,   '?-'(G),_Vs):- !, expand_goal(G,GG) -> in_space_cmt(forall(GG,portray_one_line(G))).
visit_script_term(Pos,  ':-'(G),_Vs):- !, expand_goal(G,Pos,GG,_)->in_space_cmt(GG).
visit_script_term(Pos,       T ,_Vs):- b_setval('$term',T), expand_term(T,Pos,Term,_),
   '$set_source_module'(SM, SM),
   strip_module(SM:Term, M, _Plain),
    (   M == SM
    ->  Clause = Term
    ;   Clause = M:Term
    ),
    source_location(File,Line),
    '$store_clause'('$source_location'(File, Line):Clause, File).


% :- fixup_exports.


