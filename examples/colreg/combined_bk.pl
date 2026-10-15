





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
sector(agent0,vessel1_0,port_bow_broad).
range(agent0,vessel1_0,very_far).
dcpa(agent0,vessel1_0,critical).
tcpa(agent0,vessel1_0,long).
sector(vessel1_0,agent0,starboard_bow_broad).
range(vessel1_0,agent0,very_far).
dcpa(vessel1_0,agent0,critical).
tcpa(vessel1_0,agent0,long).
sector(agent1,vessel1_1,port_bow_broad).
range(agent1,vessel1_1,far).
dcpa(agent1,vessel1_1,critical).
tcpa(agent1,vessel1_1,medium).
sector(vessel1_1,agent1,starboard_bow_broad).
range(vessel1_1,agent1,far).
dcpa(vessel1_1,agent1,critical).
tcpa(vessel1_1,agent1,medium).
sector(agent2,vessel1_2,port_bow_broad).
range(agent2,vessel1_2,middle).
dcpa(agent2,vessel1_2,critical).
tcpa(agent2,vessel1_2,short).
sector(vessel1_2,agent2,starboard_bow_broad).
range(vessel1_2,agent2,middle).
dcpa(vessel1_2,agent2,critical).
tcpa(vessel1_2,agent2,short).
sector(agent3,vessel1_3,port_bow_broad).
range(agent3,vessel1_3,very_near).
dcpa(agent3,vessel1_3,critical).
tcpa(agent3,vessel1_3,imminent).
sector(vessel1_3,agent3,starboard_bow_broad).
range(vessel1_3,agent3,very_near).
dcpa(vessel1_3,agent3,critical).
tcpa(vessel1_3,agent3,imminent).
sector(agent4,vessel1_4,ahead).
range(agent4,vessel1_4,very_far).
sector(vessel1_4,agent4,ahead).
range(vessel1_4,agent4,very_far).
waypoint_reached(vessel1_4).
sector(agent5,vessel1_5,ahead).
range(agent5,vessel1_5,very_far).
dcpa(agent5,vessel1_5,critical).
tcpa(agent5,vessel1_5,medium).
sector(vessel1_5,agent5,ahead).
range(vessel1_5,agent5,very_far).
dcpa(vessel1_5,agent5,critical).
tcpa(vessel1_5,agent5,medium).
sector(agent6,vessel1_6,ahead).
range(agent6,vessel1_6,middle).
dcpa(agent6,vessel1_6,critical).
tcpa(agent6,vessel1_6,short).
sector(vessel1_6,agent6,ahead).
range(vessel1_6,agent6,middle).
dcpa(vessel1_6,agent6,critical).
tcpa(vessel1_6,agent6,short).
sector(agent7,vessel1_7,starboard_beam_forward).
range(agent7,vessel1_7,far).
dcpa(agent7,vessel1_7,safe).
tcpa(agent7,vessel1_7,imminent).
sector(vessel1_7,agent7,starboard_bow_broad).
range(vessel1_7,agent7,far).
dcpa(vessel1_7,agent7,safe).
tcpa(vessel1_7,agent7,imminent).
sector(agent8,vessel1_8,starboard_bow_forward).
range(agent8,vessel1_8,very_far).
dcpa(agent8,vessel1_8,critical).
tcpa(agent8,vessel1_8,long).
sector(vessel1_8,agent8,port_bow_broad).
range(vessel1_8,agent8,very_far).
dcpa(vessel1_8,agent8,critical).
tcpa(vessel1_8,agent8,long).
sector(agent9,vessel1_9,starboard_bow_forward).
range(agent9,vessel1_9,middle).
dcpa(agent9,vessel1_9,critical).
tcpa(agent9,vessel1_9,short).
sector(vessel1_9,agent9,port_bow_broad).
range(vessel1_9,agent9,middle).
dcpa(vessel1_9,agent9,critical).
tcpa(vessel1_9,agent9,short).
sector(agent10,vessel1_10,starboard_bow_forward).
range(agent10,vessel1_10,far).
dcpa(agent10,vessel1_10,critical).
tcpa(agent10,vessel1_10,medium).
sector(vessel1_10,agent10,port_bow_broad).
range(vessel1_10,agent10,far).
dcpa(vessel1_10,agent10,critical).
tcpa(vessel1_10,agent10,medium).
sector(agent11,vessel1_11,ahead).
range(agent11,vessel1_11,middle).
dcpa(agent11,vessel1_11,critical).
tcpa(agent11,vessel1_11,long).
sector(vessel1_11,agent11,astern).
arc_overtaking(agent11,vessel1_11).
range(vessel1_11,agent11,middle).
dcpa(vessel1_11,agent11,critical).
tcpa(vessel1_11,agent11,long).
sector(agent12,vessel1_12,ahead).
range(agent12,vessel1_12,near).
dcpa(agent12,vessel1_12,critical).
tcpa(agent12,vessel1_12,medium).
sector(vessel1_12,agent12,astern).
arc_overtaking(agent12,vessel1_12).
range(vessel1_12,agent12,near).
dcpa(vessel1_12,agent12,critical).
tcpa(vessel1_12,agent12,medium).
sector(agent13,vessel1_13,ahead).
range(agent13,vessel1_13,very_near).
dcpa(agent13,vessel1_13,critical).
tcpa(agent13,vessel1_13,short).
sector(vessel1_13,agent13,astern).
arc_overtaking(agent13,vessel1_13).
range(vessel1_13,agent13,very_near).
dcpa(vessel1_13,agent13,critical).
tcpa(vessel1_13,agent13,short).
