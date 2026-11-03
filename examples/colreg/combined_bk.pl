





%  GEOMETRIC ABSTRACTION
port_forward(X,Y)      :- sector(X,Y,port_bow_forward).
port_forward(X,Y)      :- sector(X,Y,port_bow_broad).
port_forward(X,Y)      :- sector(X,Y,port_beam_forward).
port_aft(X,Y)          :- sector(X,Y,port_beam_aft).
port_aft(X,Y)          :- sector(X,Y,port_quarter_broad).
port_aft(X,Y)          :- sector(X,Y,port_quarter_aft).
starboard_forward(X,Y) :- sector(X,Y,starboard_bow_forward).
starboard_forward(X,Y) :- sector(X,Y,starboard_bow_broad).
starboard_forward(X,Y) :- sector(X,Y,starboard_beam_forward).
starboard_aft(X,Y)     :- sector(X,Y,starboard_beam_aft).
starboard_aft(X,Y)     :- sector(X,Y,starboard_quarter_broad).
starboard_aft(X,Y)     :- sector(X,Y,starboard_quarter_aft).

port(X,Y)      :- port_forward(X,Y).
port(X,Y)      :- port_aft(X,Y).
port(X,Y)      :- sector(X,Y,port_beam).
starboard(X,Y) :- starboard_forward(X,Y).
starboard(X,Y) :- starboard_aft(X,Y).
starboard(X,Y) :- sector(X,Y,starboard_beam).
forward(X,Y)   :- port_forward(X,Y).
forward(X,Y)   :- starboard_forward(X,Y).
forward(X,Y)   :- sector(X,Y,ahead).
aft(X,Y)       :- port_aft(X,Y).
aft(X,Y)       :- starboard_aft(X,Y).
aft(X,Y)       :- sector(X,Y,astern).


% ORDERINGS

% range
less_and_adjacent(far,very_far).
less_and_adjacent(middle,far).
less_and_adjacent(near,middle).
less_and_adjacent(very_near,near).

% tcpa
less_and_adjacent(long,very_long).
less_and_adjacent(medium,long).
less_and_adjacent(short,medium).
less_and_adjacent(imminent,short).

% dcpa
less_and_adjacent(marginal,safe).
less_and_adjacent(close,marginal).
less_and_adjacent(very_close,close).
less_and_adjacent(critical,very_close).

% turn magnitude
less_and_adjacent(large,very_large).
less_and_adjacent(moderate,large).
less_and_adjacent(small,moderate).
less_and_adjacent(insubstantial,small).

% Avoid Resume Risks
less_and_adjacent(no_risk, risk_developing).
less_and_adjacent(risk_developing, medium_close).
less_and_adjacent(medium_close, medium_veryclose).
less_and_adjacent(medium_veryclose, medium_critical).
less_and_adjacent(medium_critical, short_close).
less_and_adjacent(short_close, short_veryclose).
less_and_adjacent(short_veryclose, short_critical).
less_and_adjacent(short_critical, imminent_close).
less_and_adjacent(imminent_close, imminent_veryclose).
less_and_adjacent(imminent_veryclose, imminent_critical).

less_than(X,Y) :- 
    less_and_adjacent(X,Z), 
    less_than(Z,Y).
less_than(X,Y) :-
    less_and_adjacent(X,Y).

greater_than(X,Y) :- 
    less_and_adjacent(Z,X), 
    greater_than(Z,Y).
greater_than(X,Y) :-
    less_and_adjacent(Y,X).

less_or_equal(X,X).
less_or_equal(X,Y) :- less_than(X,Y).

greater_or_equal(X,X).
greater_or_equal(X,Y) :- greater_than(X,Y).

range_gt(X,Y,A):-
    range(X,Y,B),
    greater_than(B,A).
range_ge(X,Y,A):-
    range(X,Y,B),
    greater_or_equal(B,A).
range_lt(X,Y,A):-
    range(X,Y,B),
    less_than(B,A).
range_le(X,Y,A):-
    range(X,Y,B),
    less_or_equal(B,A).


dcpa_gt(X,Y,A):-
    dcpa(X,Y,B),
    greater_than(B,A).
dcpa_ge(X,Y,A):-
    dcpa(X,Y,B),
    greater_or_equal(B,A).
dcpa_lt(X,Y,A):-
    dcpa(X,Y,B),
    less_than(B,A).
dcpa_le(X,Y,A):-
    dcpa(X,Y,B),
    less_or_equal(B,A).

tcpa_gt(X,Y,A):-
    tcpa(X,Y,B),
    greater_than(B,A).
tcpa_ge(X,Y,A):-
    tcpa(X,Y,B),
    greater_or_equal(B,A).
tcpa_lt(X,Y,A):-
    tcpa(X,Y,B),
    less_than(B,A).
tcpa_le(X,Y,A):-
    tcpa(X,Y,B),
    less_or_equal(B,A).


%  CONCEPTUAL GROUPINGS

dcpa_acceptable(X,Y) :- dcpa(X,Y,marginal).
dcpa_acceptable(X,Y) :- dcpa(X,Y,safe).
dcpa_unacceptable(X,Y) :- not(dcpa_acceptable(X,Y)).

tcpa_closing(X,Y) :- not(tcpa(X,Y,opening)).

actionable_range(X,Y) :- not(range(X,Y,very_far)).


%  ample_time  (Rule 8(a))

ample_time(X,Y)    :- tcpa(X,Y,medium).
ample_time(X,Y)    :- tcpa(X,Y,long).
ample_time(X,Y)    :- tcpa(X,Y,very_long).



%  RISK OF COLLISION (Rule 7)

collision_risk(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,imminent).
collision_risk(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,short).
collision_risk(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,medium).


%  CLOSE-QUARTERS SITUATION (Rule 8)

close_quarters_developing(X,Y) :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,far).
close_quarters_developing(X,Y) :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,middle).
close_quarters(X,Y)            :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,near).
close_quarters(X,Y)            :- dcpa_unacceptable(X,Y), tcpa_closing(X,Y), range(X,Y,very_near).


%  ENCOUNTER  (three types, one per pair) - the finding of fact

encounter(X,Y,rule13_overtaking) :-
    collision_risk(X,Y),
    arc_overtaking(X,Y).

encounter(X,Y,rule14_head_on) :-
    collision_risk(X,Y),
    mutual_ahead(X,Y),
    not(arc_overtaking(X,Y)),
    not(arc_overtaking(Y,X)).

encounter(X,Y,rule15_crossing) :-
    collision_risk(X,Y),
    not(arc_overtaking(X,Y)),
    not(arc_overtaking(Y,X)),
    not(mutual_ahead(X,Y)).

mutual_ahead(X,Y):-
    sector(X,Y,ahead),
    sector(Y,X,ahead).


%  ENCOUNTER + CONDUCT  (Own, Target, Encounter, Conduct) - the conclusion of law
encounter_and_conduct(X,Y,rule13_overtaking,rule16_giveway) :- encounter(X,Y,rule13_overtaking).   % X overtakes Y
encounter_and_conduct(X,Y,rule13_overtaking,rule17_standon_maintain) :- encounter(Y,X,rule13_overtaking), ample_time(X,Y).   % Y overtakes X
encounter_and_conduct(X,Y,rule13_overtaking,rule17_standon_may_act) :- encounter(Y,X,rule13_overtaking), tcpa(X,Y,short).   % Y overtakes X
encounter_and_conduct(X,Y,rule13_overtaking,rule17_standon_must_act) :- encounter(Y,X,rule13_overtaking), tcpa(X,Y,imminent).   % Y overtakes X
encounter_and_conduct(X,Y,rule14_head_on,rule16_giveway)    :- encounter(X,Y,rule14_head_on).        % head-on: mutual
encounter_and_conduct(X,Y,rule15_crossing,rule16_giveway)   :- encounter(X,Y,rule15_crossing), starboard(X,Y).
encounter_and_conduct(X,Y,rule15_crossing,rule16_giveway)   :- encounter(X,Y,rule15_crossing), port(Y,X).
encounter_and_conduct(X,Y,rule15_crossing,rule17_standon_maintain)   :- encounter(X,Y,rule15_crossing), port(X,Y), ample_time(X,Y).
encounter_and_conduct(X,Y,rule15_crossing,rule17_standon_maintain)   :- encounter(X,Y,rule15_crossing), starboard(Y,X), ample_time(X,Y).
encounter_and_conduct(X,Y,rule15_crossing,rule17_standon_may_act)   :- encounter(X,Y,rule15_crossing), port(X,Y), tcpa(X,Y,short).
encounter_and_conduct(X,Y,rule15_crossing,rule17_standon_may_act)   :- encounter(X,Y,rule15_crossing), starboard(Y,X), tcpa(X,Y,short).
encounter_and_conduct(X,Y,rule15_crossing,rule17_standon_must_act)   :- encounter(X,Y,rule15_crossing), port(X,Y), tcpa(X,Y,imminent).
encounter_and_conduct(X,Y,rule15_crossing,rule17_standon_must_act)   :- encounter(X,Y,rule15_crossing), starboard(Y,X), tcpa(X,Y,imminent).


%  DUTY 
duty(X,Y,rule16_giveway) :- encounter_and_conduct(X,Y,_,rule16_giveway).
duty(X,Y,rule17_standon) :- encounter_and_conduct(X,Y,_,rule17_standon_maintain).
duty(X,Y,rule17_standon) :- encounter_and_conduct(X,Y,_,rule17_standon_may_act).
duty(X,Y,rule17_standon) :- encounter_and_conduct(X,Y,_,rule17_standon_must_act).


%  EMERGENCY  - in extremis, departure from any rule; encounter-agnostic (Rule 2(b))

rule2_extremis(X,Y) :- dcpa_unacceptable(X,Y), tcpa(X,Y,imminent).
%might be a cleaner way to do this
sector(agent_crossing2_0,vessel1_crossing2_0,port_bow_broad).
range(agent_crossing2_0,vessel1_crossing2_0,very_far).
dcpa(agent_crossing2_0,vessel1_crossing2_0,critical).
tcpa(agent_crossing2_0,vessel1_crossing2_0,long).
sector(vessel1_crossing2_0,agent_crossing2_0,starboard_bow_broad).
range(vessel1_crossing2_0,agent_crossing2_0,very_far).
dcpa(vessel1_crossing2_0,agent_crossing2_0,critical).
tcpa(vessel1_crossing2_0,agent_crossing2_0,long).
sector(agent_crossing2_1,vessel1_crossing2_1,port_bow_broad).
range(agent_crossing2_1,vessel1_crossing2_1,far).
dcpa(agent_crossing2_1,vessel1_crossing2_1,critical).
tcpa(agent_crossing2_1,vessel1_crossing2_1,medium).
sector(vessel1_crossing2_1,agent_crossing2_1,starboard_bow_broad).
range(vessel1_crossing2_1,agent_crossing2_1,far).
dcpa(vessel1_crossing2_1,agent_crossing2_1,critical).
tcpa(vessel1_crossing2_1,agent_crossing2_1,medium).
sector(agent_crossing2_2,vessel1_crossing2_2,port_bow_broad).
range(agent_crossing2_2,vessel1_crossing2_2,middle).
dcpa(agent_crossing2_2,vessel1_crossing2_2,critical).
tcpa(agent_crossing2_2,vessel1_crossing2_2,short).
sector(vessel1_crossing2_2,agent_crossing2_2,starboard_bow_broad).
range(vessel1_crossing2_2,agent_crossing2_2,middle).
dcpa(vessel1_crossing2_2,agent_crossing2_2,critical).
tcpa(vessel1_crossing2_2,agent_crossing2_2,short).
sector(agent_crossing2_3,cruiseliner1_crossing2_3,port_bow_broad).
range(agent_crossing2_3,cruiseliner1_crossing2_3,very_near).
dcpa(agent_crossing2_3,cruiseliner1_crossing2_3,critical).
tcpa(agent_crossing2_3,cruiseliner1_crossing2_3,imminent).
sector(cruiseliner1_crossing2_3,agent_crossing2_3,starboard_bow_broad).
range(cruiseliner1_crossing2_3,agent_crossing2_3,very_near).
dcpa(cruiseliner1_crossing2_3,agent_crossing2_3,critical).
tcpa(cruiseliner1_crossing2_3,agent_crossing2_3,imminent).
sector(agent_headon1_0,cruiseliner1_headon1_0,ahead).
range(agent_headon1_0,cruiseliner1_headon1_0,very_far).
dcpa(agent_headon1_0,cruiseliner1_headon1_0,critical).
tcpa(agent_headon1_0,cruiseliner1_headon1_0,long).
sector(cruiseliner1_headon1_0,agent_headon1_0,ahead).
range(cruiseliner1_headon1_0,agent_headon1_0,very_far).
dcpa(cruiseliner1_headon1_0,agent_headon1_0,critical).
tcpa(cruiseliner1_headon1_0,agent_headon1_0,long).
sector(agent_headon1_1,vessel1_headon1_1,ahead).
range(agent_headon1_1,vessel1_headon1_1,very_far).
dcpa(agent_headon1_1,vessel1_headon1_1,critical).
tcpa(agent_headon1_1,vessel1_headon1_1,medium).
sector(vessel1_headon1_1,agent_headon1_1,ahead).
range(vessel1_headon1_1,agent_headon1_1,very_far).
dcpa(vessel1_headon1_1,agent_headon1_1,critical).
tcpa(vessel1_headon1_1,agent_headon1_1,medium).
sector(agent_headon1_2,vessel1_headon1_2,ahead).
range(agent_headon1_2,vessel1_headon1_2,middle).
dcpa(agent_headon1_2,vessel1_headon1_2,critical).
tcpa(agent_headon1_2,vessel1_headon1_2,short).
sector(vessel1_headon1_2,agent_headon1_2,ahead).
range(vessel1_headon1_2,agent_headon1_2,middle).
dcpa(vessel1_headon1_2,agent_headon1_2,critical).
tcpa(vessel1_headon1_2,agent_headon1_2,short).
sector(agent_passing1_0,vessel1_passing1_0,starboard_beam_forward).
range(agent_passing1_0,vessel1_passing1_0,far).
dcpa(agent_passing1_0,vessel1_passing1_0,safe).
tcpa(agent_passing1_0,vessel1_passing1_0,imminent).
sector(vessel1_passing1_0,agent_passing1_0,starboard_bow_broad).
range(vessel1_passing1_0,agent_passing1_0,far).
dcpa(vessel1_passing1_0,agent_passing1_0,safe).
tcpa(vessel1_passing1_0,agent_passing1_0,imminent).
sector(agent_crossing1_0,vessel1_crossing1_0,starboard_bow_forward).
range(agent_crossing1_0,vessel1_crossing1_0,very_far).
dcpa(agent_crossing1_0,vessel1_crossing1_0,critical).
tcpa(agent_crossing1_0,vessel1_crossing1_0,long).
sector(vessel1_crossing1_0,agent_crossing1_0,port_bow_broad).
range(vessel1_crossing1_0,agent_crossing1_0,very_far).
dcpa(vessel1_crossing1_0,agent_crossing1_0,critical).
tcpa(vessel1_crossing1_0,agent_crossing1_0,long).
sector(agent_crossing1_1,vessel1_crossing1_1,starboard_bow_forward).
range(agent_crossing1_1,vessel1_crossing1_1,middle).
dcpa(agent_crossing1_1,vessel1_crossing1_1,critical).
tcpa(agent_crossing1_1,vessel1_crossing1_1,short).
sector(vessel1_crossing1_1,agent_crossing1_1,port_bow_broad).
range(vessel1_crossing1_1,agent_crossing1_1,middle).
dcpa(vessel1_crossing1_1,agent_crossing1_1,critical).
tcpa(vessel1_crossing1_1,agent_crossing1_1,short).
sector(agent_crossing1_2,vessel1_crossing1_2,starboard_bow_forward).
range(agent_crossing1_2,vessel1_crossing1_2,far).
dcpa(agent_crossing1_2,vessel1_crossing1_2,critical).
tcpa(agent_crossing1_2,vessel1_crossing1_2,medium).
sector(vessel1_crossing1_2,agent_crossing1_2,port_bow_broad).
range(vessel1_crossing1_2,agent_crossing1_2,far).
dcpa(vessel1_crossing1_2,agent_crossing1_2,critical).
tcpa(vessel1_crossing1_2,agent_crossing1_2,medium).
sector(agent_crossing1_3,cruiseliner1_crossing1_3,starboard_bow_forward).
range(agent_crossing1_3,cruiseliner1_crossing1_3,very_near).
dcpa(agent_crossing1_3,cruiseliner1_crossing1_3,critical).
tcpa(agent_crossing1_3,cruiseliner1_crossing1_3,imminent).
sector(cruiseliner1_crossing1_3,agent_crossing1_3,port_bow_broad).
range(cruiseliner1_crossing1_3,agent_crossing1_3,very_near).
dcpa(cruiseliner1_crossing1_3,agent_crossing1_3,critical).
tcpa(cruiseliner1_crossing1_3,agent_crossing1_3,imminent).
sector(agent_overtaking1_0,vessel1_overtaking1_0,ahead).
range(agent_overtaking1_0,vessel1_overtaking1_0,middle).
dcpa(agent_overtaking1_0,vessel1_overtaking1_0,critical).
tcpa(agent_overtaking1_0,vessel1_overtaking1_0,long).
sector(vessel1_overtaking1_0,agent_overtaking1_0,astern).
arc_overtaking(agent_overtaking1_0,vessel1_overtaking1_0).
range(vessel1_overtaking1_0,agent_overtaking1_0,middle).
dcpa(vessel1_overtaking1_0,agent_overtaking1_0,critical).
tcpa(vessel1_overtaking1_0,agent_overtaking1_0,long).
sector(agent_overtaking1_1,vessel1_overtaking1_1,ahead).
range(agent_overtaking1_1,vessel1_overtaking1_1,near).
dcpa(agent_overtaking1_1,vessel1_overtaking1_1,critical).
tcpa(agent_overtaking1_1,vessel1_overtaking1_1,medium).
sector(vessel1_overtaking1_1,agent_overtaking1_1,astern).
arc_overtaking(agent_overtaking1_1,vessel1_overtaking1_1).
range(vessel1_overtaking1_1,agent_overtaking1_1,near).
dcpa(vessel1_overtaking1_1,agent_overtaking1_1,critical).
tcpa(vessel1_overtaking1_1,agent_overtaking1_1,medium).
sector(agent_overtaking1_2,vessel1_overtaking1_2,ahead).
range(agent_overtaking1_2,vessel1_overtaking1_2,very_near).
dcpa(agent_overtaking1_2,vessel1_overtaking1_2,critical).
tcpa(agent_overtaking1_2,vessel1_overtaking1_2,short).
sector(vessel1_overtaking1_2,agent_overtaking1_2,astern).
arc_overtaking(agent_overtaking1_2,vessel1_overtaking1_2).
range(vessel1_overtaking1_2,agent_overtaking1_2,very_near).
dcpa(vessel1_overtaking1_2,agent_overtaking1_2,critical).
tcpa(vessel1_overtaking1_2,agent_overtaking1_2,short).
sector(agent_overtaking1_3,cruiseliner1_overtaking1_3,ahead).
range(agent_overtaking1_3,cruiseliner1_overtaking1_3,very_near).
dcpa(agent_overtaking1_3,cruiseliner1_overtaking1_3,critical).
tcpa(agent_overtaking1_3,cruiseliner1_overtaking1_3,imminent).
sector(cruiseliner1_overtaking1_3,agent_overtaking1_3,astern).
arc_overtaking(agent_overtaking1_3,cruiseliner1_overtaking1_3).
range(cruiseliner1_overtaking1_3,agent_overtaking1_3,very_near).
dcpa(cruiseliner1_overtaking1_3,agent_overtaking1_3,critical).
tcpa(cruiseliner1_overtaking1_3,agent_overtaking1_3,imminent).
