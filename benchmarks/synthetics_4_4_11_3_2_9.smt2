(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun b0 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 6013226944956255 9007199254740992) r3))) (let ((.def_1 (* (- (/ 7323856827784021 9007199254740992)) r2))) (let ((.def_2 (* (- (/ 821644044036567 2251799813685248)) r1))) (let ((.def_3 (* (- (/ 5741371801822283 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 2688166169456119 4503599627370496))))) (let ((.def_6 (* (- (/ 1697553532908013 2251799813685248)) r3))) (let ((.def_7 (* (- (/ 222890304586149 9007199254740992)) r2))) (let ((.def_8 (* (- (/ 859174311696807 4503599627370496)) r1))) (let ((.def_9 (* (/ 8405258064092151 4503599627370496) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 1706834753877219 4503599627370496)))) (let ((.def_12 (or b0 .def_11 .def_5))) (let ((.def_13 (* (- (/ 436969304582399 2251799813685248)) r3))) (let ((.def_14 (* (- (/ 7897802334758829 9007199254740992)) r2))) (let ((.def_15 (* (/ 1304568605267127 9007199254740992) r1))) (let ((.def_16 (* (- (/ 740180205794337 9007199254740992)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (- (/ 1546000321873413 4503599627370496))))) (let ((.def_19 (* (- (/ 6084770197067815 4503599627370496)) r3))) (let ((.def_20 (* (/ 570967242389817 1125899906842624) r2))) (let ((.def_21 (* (- (/ 2099030186560465 4503599627370496)) r1))) (let ((.def_22 (* (- (/ 1058059220690661 9007199254740992)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 8400762168655653 9007199254740992))))) (let ((.def_25 (or b3 .def_24 .def_18))) (let ((.def_26 (* (/ 1346585403971539 2251799813685248) r3))) (let ((.def_27 (* (- (/ 3846177129718935 4503599627370496)) r2))) (let ((.def_28 (* (- (/ 3059998312248103 2251799813685248)) r1))) (let ((.def_29 (* (- (/ 1890958145040625 2251799813685248)) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (- (/ 2014432151942183 2251799813685248))))) (let ((.def_32 (* (- (/ 6042217954450965 9007199254740992)) r3))) (let ((.def_33 (* (- (/ 3489008460521109 4503599627370496)) r2))) (let ((.def_34 (* (/ 2074690743181373 9007199254740992) r1))) (let ((.def_35 (* (/ 3640814355083429 2251799813685248) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 857033350875785 4503599627370496)))) (let ((.def_38 (not b0))) (let ((.def_39 (or .def_38 .def_37 .def_31))) (let ((.def_40 (* (- (/ 413630147810027 9007199254740992)) r3))) (let ((.def_41 (* (/ 2941911874991591 2251799813685248) r2))) (let ((.def_42 (* (- (/ 3812899501703045 4503599627370496)) r1))) (let ((.def_43 (* (- (/ 286037104131903 4503599627370496)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (/ 3038392073264133 4503599627370496)))) (let ((.def_46 (* (/ 19738877404495 2251799813685248) r3))) (let ((.def_47 (* (/ 3277009485289019 9007199254740992) r2))) (let ((.def_48 (* (/ 89061822549055 562949953421312) r1))) (let ((.def_49 (* (- (/ 4256944918481571 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 116406539633469 4503599627370496))))) (let ((.def_52 (or b2 .def_51 .def_45))) (let ((.def_53 (* (- (/ 378386004712109 4503599627370496)) r3))) (let ((.def_54 (* (/ 3355858773605645 4503599627370496) r2))) (let ((.def_55 (* (/ 1192235800634205 2251799813685248) r1))) (let ((.def_56 (* (- (/ 3632468020678359 2251799813685248)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 688012035258745 4503599627370496)))) (let ((.def_59 (* (/ 968335582902919 2251799813685248) r3))) (let ((.def_60 (* (- (/ 3375742765750879 4503599627370496)) r2))) (let ((.def_61 (* (/ 1480489110357519 1125899906842624) r1))) (let ((.def_62 (* (/ 1803504098405877 4503599627370496) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 2752398023427737 4503599627370496)))) (let ((.def_65 (or b2 .def_64 .def_58))) (let ((.def_66 (* (- (/ 3464725527371707 4503599627370496)) r3))) (let ((.def_67 (* (/ 5599030386750709 9007199254740992) r2))) (let ((.def_68 (* (/ 1548872929521817 2251799813685248) r1))) (let ((.def_69 (* (/ 6871148997771613 9007199254740992) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 4258057083365105 4503599627370496)))) (let ((.def_72 (* (/ 59642464274841 70368744177664) r3))) (let ((.def_73 (* (/ 198615825534817 562949953421312) r2))) (let ((.def_74 (* (- (/ 553662900041599 281474976710656)) r1))) (let ((.def_75 (* (/ 5970797425582189 9007199254740992) r0))) (let ((.def_76 (+ .def_75 .def_74 .def_73 .def_72))) (let ((.def_77 (<= .def_76 (- (/ 96143043182295 562949953421312))))) (let ((.def_78 (or b3 .def_77 .def_71))) (let ((.def_79 (* (- (/ 6035349143834175 2251799813685248)) r3))) (let ((.def_80 (* (/ 4127181916179137 4503599627370496) r2))) (let ((.def_81 (* (/ 2216347159073857 2251799813685248) r1))) (let ((.def_82 (* (- (/ 588567717472541 562949953421312)) r0))) (let ((.def_83 (+ .def_82 .def_81 .def_80 .def_79))) (let ((.def_84 (<= .def_83 (- (/ 94855355009233 2251799813685248))))) (let ((.def_85 (* (- (/ 2131437282713695 4503599627370496)) r3))) (let ((.def_86 (* (/ 3975217028107911 4503599627370496) r2))) (let ((.def_87 (* (- (/ 3215361189784719 4503599627370496)) r1))) (let ((.def_88 (* (- (/ 548041986733043 9007199254740992)) r0))) (let ((.def_89 (+ .def_88 .def_87 .def_86 .def_85))) (let ((.def_90 (<= .def_89 (- (/ 2351616645695951 9007199254740992))))) (let ((.def_91 (not b2))) (let ((.def_92 (or .def_91 .def_90 .def_84))) (let ((.def_93 (* (/ 4445659814114135 9007199254740992) r3))) (let ((.def_94 (* (- (/ 127572037930789 2251799813685248)) r2))) (let ((.def_95 (* (/ 1380959324117199 9007199254740992) r1))) (let ((.def_96 (* (- (/ 4048242666597141 4503599627370496)) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (- (/ 155328461952611 1125899906842624))))) (let ((.def_99 (* (- (/ 2790760589786977 9007199254740992)) r3))) (let ((.def_100 (* (- (/ 5741599332146303 9007199254740992)) r2))) (let ((.def_101 (* (/ 2527814138700731 4503599627370496) r1))) (let ((.def_102 (* (/ 3032140617928043 2251799813685248) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (/ 3811413524435189 9007199254740992)))) (let ((.def_105 (or b2 .def_104 .def_98))) (let ((.def_106 (* (/ 2588204449068213 2251799813685248) r3))) (let ((.def_107 (* (- (/ 240039474251035 140737488355328)) r2))) (let ((.def_108 (* (- (/ 3741608579544717 9007199254740992)) r1))) (let ((.def_109 (* (/ 2220443986640235 9007199254740992) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 1759315585897135 9007199254740992)))) (let ((.def_112 (* (/ 1679032195376557 2251799813685248) r3))) (let ((.def_113 (* (/ 6681357748749669 9007199254740992) r2))) (let ((.def_114 (* (- (/ 326153097822427 281474976710656)) r1))) (let ((.def_115 (* (- (/ 3704240825984115 9007199254740992)) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 1413060741830583 9007199254740992))))) (let ((.def_118 (or b0 .def_117 .def_111))) (let ((.def_119 (* (- (/ 7912220416349829 9007199254740992)) r3))) (let ((.def_120 (* (- (/ 2414951543230343 4503599627370496)) r2))) (let ((.def_121 (* (/ 1477566310580059 4503599627370496) r1))) (let ((.def_122 (* (- (/ 605365975037081 2251799813685248)) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (- (/ 241163186591091 562949953421312))))) (let ((.def_125 (* (- (/ 1576287358281251 4503599627370496)) r3))) (let ((.def_126 (* (/ 2801640137795947 4503599627370496) r2))) (let ((.def_127 (* (- (/ 635857073633439 562949953421312)) r1))) (let ((.def_128 (* (/ 2802755672072607 1125899906842624) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (/ 7493830577991629 9007199254740992)))) (let ((.def_131 (or .def_38 .def_130 .def_124))) (let ((.def_132 (* (- (/ 582775002793195 562949953421312)) r3))) (let ((.def_133 (* (- (/ 948373755944827 562949953421312)) r2))) (let ((.def_134 (* (- (/ 48710990588421 9007199254740992)) r1))) (let ((.def_135 (* (- (/ 3763280663907351 1125899906842624)) r0))) (let ((.def_136 (+ .def_135 .def_134 .def_133 .def_132))) (let ((.def_137 (<= .def_136 (- (/ 3707117943696199 2251799813685248))))) (let ((.def_138 (* (/ 2504207743266427 2251799813685248) r3))) (let ((.def_139 (* (/ 3155262607569113 4503599627370496) r2))) (let ((.def_140 (* (- (/ 1610540170181689 9007199254740992)) r1))) (let ((.def_141 (* (- (/ 5911776444379543 4503599627370496)) r0))) (let ((.def_142 (+ .def_141 .def_140 .def_139 .def_138))) (let ((.def_143 (<= .def_142 (/ 56805536816263 562949953421312)))) (let ((.def_144 (not b3))) (let ((.def_145 (or .def_144 .def_143 .def_137))) (let ((.def_146 (and .def_145 .def_131 .def_118 .def_105 .def_92 .def_78 .def_65 .def_52 .def_39 .def_25 .def_12))) .def_146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)