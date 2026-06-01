% POSITIVES — contain an -OH (oxygen, single-bonded, exactly one H)
methanol((n/a, c, [h, h, h, (1, o, [h])])).
ethanol((n/a, c, [h, h, h, (1, c, [h, h, (1, o, [h])])])).
propan_1_ol((n/a, c, [h, h, h, (1, c, [h, h, (1, c, [h, h, (1, o, [h])])])])).

% NEGATIVES — no -OH
methane((n/a, c, [h, h, h, h])).
ethane((n/a, c, [h, h, h, (1, c, [h, h, h])])).
dimethyl_ether((n/a, c, [h, h, h, (1, o, [(1, c, [h, h, h])])])).  % has O, but O–C not O–H
formaldehyde((n/a, c, [h, h, (2, o, [])])).                       % has O, but C=O not O–H
methanethiol((n/a, c, [h, h, h, (1, s, [h])])).      %  -SH