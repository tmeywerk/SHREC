(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b0 () Bool)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 2565928724892373 4503599627370496) r3))) (let ((.def_1 (* (- (/ 468029367333997 281474976710656)) r2))) (let ((.def_2 (* (- (/ 12648445608435 281474976710656)) r1))) (let ((.def_3 (* (/ 7383450167674859 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 354632526635847 9007199254740992)))) (let ((.def_6 (* (- (/ 583597676308657 1125899906842624)) r3))) (let ((.def_7 (* (- (/ 2116002259309455 4503599627370496)) r2))) (let ((.def_8 (* (/ 5541064087767859 4503599627370496) r1))) (let ((.def_9 (* (/ 855864881556805 562949953421312) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 2399468341087247 4503599627370496)))) (let ((.def_12 (or b2 .def_11 .def_5))) (let ((.def_13 (* (/ 4232140915760837 4503599627370496) r3))) (let ((.def_14 (* (- (/ 4581947124475895 4503599627370496)) r2))) (let ((.def_15 (* (/ 396719303640157 562949953421312) r1))) (let ((.def_16 (* (- (/ 631141182877653 9007199254740992)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 1867170293857263 4503599627370496)))) (let ((.def_19 (* (/ 710353906672047 562949953421312) r3))) (let ((.def_20 (* (/ 3537650321267957 4503599627370496) r2))) (let ((.def_21 (* (- (/ 3951563507407647 9007199254740992)) r1))) (let ((.def_22 (* (- (/ 4112562496699325 4503599627370496)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (/ 2729166472397323 9007199254740992)))) (let ((.def_25 (not b0))) (let ((.def_26 (or .def_25 .def_24 .def_18))) (let ((.def_27 (* (/ 828071352716703 9007199254740992) r3))) (let ((.def_28 (* (/ 8606938566200757 9007199254740992) r2))) (let ((.def_29 (* (/ 3218402218029543 2251799813685248) r1))) (let ((.def_30 (* (/ 1244377954856521 1125899906842624) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 5193234156318109 2251799813685248)))) (let ((.def_33 (* (- (/ 2555292072704729 1125899906842624)) r3))) (let ((.def_34 (* (/ 1939638604836899 1125899906842624) r2))) (let ((.def_35 (* (- (/ 431740940610993 4503599627370496)) r1))) (let ((.def_36 (* (- (/ 2259189216841455 2251799813685248)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 7572588615939259 9007199254740992))))) (let ((.def_39 (or b1 .def_38 .def_32))) (let ((.def_40 (* (- (/ 1872552035916513 9007199254740992)) r3))) (let ((.def_41 (* (- (/ 2631986871133913 1125899906842624)) r2))) (let ((.def_42 (* (- (/ 8847458066084587 4503599627370496)) r1))) (let ((.def_43 (* (/ 3800922247258941 9007199254740992) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (- (/ 7227223097704367 9007199254740992))))) (let ((.def_46 (* (- (/ 1244129458693503 2251799813685248)) r3))) (let ((.def_47 (* (- (/ 5354135226526177 4503599627370496)) r2))) (let ((.def_48 (* (- (/ 294160255329191 562949953421312)) r1))) (let ((.def_49 (* (- (/ 1370531291828687 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 6042755480567857 4503599627370496))))) (let ((.def_52 (or b1 .def_51 .def_45))) (let ((.def_53 (* (- (/ 331015478855209 562949953421312)) r3))) (let ((.def_54 (* (- (/ 2972185188292383 2251799813685248)) r2))) (let ((.def_55 (* (/ 3114489057690005 2251799813685248) r1))) (let ((.def_56 (* (/ 3019717138751935 4503599627370496) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 3356563461752911 9007199254740992)))) (let ((.def_59 (* (- (/ 759351988042065 1125899906842624)) r3))) (let ((.def_60 (* (/ 148808967507793 140737488355328) r2))) (let ((.def_61 (* (/ 6368862905280153 9007199254740992) r1))) (let ((.def_62 (* (- (/ 1913910561744803 9007199254740992)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 1811269465776999 4503599627370496)))) (let ((.def_65 (not b3))) (let ((.def_66 (or .def_65 .def_64 .def_58))) (let ((.def_67 (* (- (/ 2055753714437093 4503599627370496)) r3))) (let ((.def_68 (* (/ 859109548110553 1125899906842624) r2))) (let ((.def_69 (* (- (/ 1378244229971225 9007199254740992)) r1))) (let ((.def_70 (* (/ 393177785677083 9007199254740992) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 395811903898541 2251799813685248)))) (let ((.def_73 (* (/ 716809134782887 2251799813685248) r3))) (let ((.def_74 (* (- (/ 4418393240818681 2251799813685248)) r2))) (let ((.def_75 (* (/ 954295610822503 4503599627370496) r1))) (let ((.def_76 (* (/ 3744333239726709 9007199254740992) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 3525112762792455 4503599627370496))))) (let ((.def_79 (or b2 .def_78 .def_72))) (let ((.def_80 (* (/ 640471153418337 562949953421312) r3))) (let ((.def_81 (* (- (/ 2368357231045629 4503599627370496)) r2))) (let ((.def_82 (* (/ 416401617161507 281474976710656) r1))) (let ((.def_83 (* (/ 359618038990367 2251799813685248) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 2842824778780511 2251799813685248)))) (let ((.def_86 (* (- (/ 3678907343056239 1125899906842624)) r3))) (let ((.def_87 (* (/ 2536282461463173 2251799813685248) r2))) (let ((.def_88 (* (- (/ 1880729789781741 9007199254740992)) r1))) (let ((.def_89 (* (/ 3083299430289173 2251799813685248) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (- (/ 1860249833679951 4503599627370496))))) (let ((.def_92 (not b2))) (let ((.def_93 (or .def_92 .def_91 .def_85))) (let ((.def_94 (* (- (/ 415867534961105 1125899906842624)) r3))) (let ((.def_95 (* (/ 3750519831940253 4503599627370496) r2))) (let ((.def_96 (* (/ 3736172856784707 4503599627370496) r1))) (let ((.def_97 (* (- (/ 384714642101507 140737488355328)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (/ 4294309907416339 9007199254740992)))) (let ((.def_100 (* (/ 8569172045995365 9007199254740992) r3))) (let ((.def_101 (* (/ 2930331241251453 4503599627370496) r2))) (let ((.def_102 (* (/ 2308184945644603 4503599627370496) r1))) (let ((.def_103 (* (- (/ 712129226940469 1125899906842624)) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (/ 1430647982420801 2251799813685248)))) (let ((.def_106 (or .def_25 .def_105 .def_99))) (let ((.def_107 (* (- (/ 242935908448689 4503599627370496)) r3))) (let ((.def_108 (* (- (/ 883045608198167 1125899906842624)) r2))) (let ((.def_109 (* (/ 7854143217333733 4503599627370496) r1))) (let ((.def_110 (* (/ 4132066805772469 4503599627370496) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (/ 2508782219304335 2251799813685248)))) (let ((.def_113 (* (- (/ 5180920119420349 9007199254740992)) r3))) (let ((.def_114 (* (- (/ 8946810317152019 9007199254740992)) r2))) (let ((.def_115 (* (- (/ 4189084018510903 2251799813685248)) r1))) (let ((.def_116 (* (/ 1466455221252639 4503599627370496) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (- (/ 7380983911233337 4503599627370496))))) (let ((.def_119 (or b3 .def_118 .def_112))) (let ((.def_120 (* (/ 2549032245590247 1125899906842624) r3))) (let ((.def_121 (* (- (/ 4273093007740279 2251799813685248)) r2))) (let ((.def_122 (* (- (/ 6830881413058423 9007199254740992)) r1))) (let ((.def_123 (* (- (/ 7858310990756777 9007199254740992)) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (/ 651499583523991 9007199254740992)))) (let ((.def_126 (* (- (/ 2337642142996289 4503599627370496)) r3))) (let ((.def_127 (* (/ 38061773779997 70368744177664) r2))) (let ((.def_128 (* (/ 453439499263649 140737488355328) r1))) (let ((.def_129 (* (- (/ 158686977157533 2251799813685248)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (/ 1252969225407127 1125899906842624)))) (let ((.def_132 (or .def_25 .def_131 .def_125))) (let ((.def_133 (* (- (/ 8902790052214665 9007199254740992)) r3))) (let ((.def_134 (* (- (/ 3174907139898793 1125899906842624)) r2))) (let ((.def_135 (* (/ 2266772071872611 9007199254740992) r1))) (let ((.def_136 (* (/ 429585113478503 4503599627370496) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 1010980329702061 2251799813685248))))) (let ((.def_139 (* (/ 218930227062651 4503599627370496) r3))) (let ((.def_140 (* (- (/ 8845941058558757 9007199254740992)) r2))) (let ((.def_141 (* (/ 1553765232101581 2251799813685248) r1))) (let ((.def_142 (* (- (/ 633717819384561 2251799813685248)) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (- (/ 2846305209405119 9007199254740992))))) (let ((.def_145 (or b2 .def_144 .def_138))) (let ((.def_146 (* (/ 3519243208997733 2251799813685248) r3))) (let ((.def_147 (* (/ 115844735906447 4503599627370496) r2))) (let ((.def_148 (* (- (/ 556617290840607 1125899906842624)) r1))) (let ((.def_149 (* (/ 1518703265796547 4503599627370496) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 1491921812261999 1125899906842624)))) (let ((.def_152 (* (/ 1777128184681181 9007199254740992) r3))) (let ((.def_153 (* (/ 1254678221441659 562949953421312) r2))) (let ((.def_154 (* (- (/ 8919668539559079 4503599627370496)) r1))) (let ((.def_155 (* (/ 5363183174823199 9007199254740992) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (/ 2637297993411403 4503599627370496)))) (let ((.def_158 (not b1))) (let ((.def_159 (or .def_158 .def_157 .def_151))) (let ((.def_160 (and .def_159 .def_145 .def_132 .def_119 .def_106 .def_93 .def_79 .def_66 .def_52 .def_39 .def_26 .def_12))) .def_160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
