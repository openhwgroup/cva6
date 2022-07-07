(VIssue interface
p0
ccopy_reg
_reconstructor
p1
(cvp_pack
Ip
p2
c__builtin__
object
p3
Ntp4
Rp5
(dp6
Vprop_count
p7
I2
sVname
p8
g0
sVprop_list
p9
(dp10
sVip_num
p11
I0
sVwid_order
p12
I0
sVchecklist
p13
(lp14
(lp15
VDesign Spec Approval
p16
aVDate:\u000a\u000aAttendees:\u000a\u000aStandalone Spec Hash:\u000a\u000aBlock Diagram Review:\u000a\u000aSpare Cells:\u000a\u000aGeneral comments:
p17
aI0
aa(lp18
VReset Status
p19
aVAsynchronous (Re)set:\u000a	- Logic under reset in the same clock domain than reset sources?\u000a\u000aSynchronous (Re)set:\u000a	- Modules / Regs / Justification\u000a\u000aReset exceptions:\u000a	- Modules / Regs / Justification\u000a\u000aLogic on reset tree:\u000a	- Modules / Clock Domain / Justification\u000a\u000aImpact of POR on IP:\u000a\u000aImpact of system Reset on IP:\u000a
p20
aI0
aa(lp21
VClock Status
p22
aVClock Domains:\u000a\u000aAsynchronism:\u000a    - Resynchro Design Solution\u000a\u000aIP asynchronous logic with regard to system clock domain:\u000a\u000aHarcoded Gated Clock / Logic on clock tree:\u000a\u000aFalling edge FF:\u000a\u000aLatches:\u000a\u000aImpact of system clock stealer on IP:\u000a\u000aImpact of random clock stealer on IP:\u000a\u000aImpact of PKI clock stealer on IP:\u000a
p23
aI0
aa(lp24
VIntegration Status
p25
aVImpact of Interrupts on IP:\u000a\u000aImpact of IP configuration change while IP is running:\u000a\u000aImpact of standby entry/resume on IP\u000a\u000aImpact of wfe/wfi on IP:\u000a\u000aImpact of Flash wait state configuration/change on IP:\u000a\u000aImpact of Instruction Cache enable/disable on IP:\u000a\u000aImpact of Instruction Cache flush on IP:\u000a\u000aIP toggling nets when not used:
p26
aI0
aa(lp27
VRTL Code Review
p28
aVDate:\u000a\u000aAttendees:\u000a\u000aRTL Hash:\u000a\u000aGeneral comments:\u000a\u000a
p29
aI0
aa(lp30
VSynthesis Status
p31
aVSDC Constraints:\u000a\u000aFalling edge triggered logic:\u000a\u000alatches:\u000a\u000aWarning:\u000a
p32
aI0
aa(lp33
VHAL Status
p34
aV
p35
aI0
aa(lp36
VSpyglass Status
p37
ag35
aI0
aa(lp38
VCode Coverage Status
p39
aVRTL Coverage Status at top level:\u000a
p40
aI0
aa(lp41
VCertitude at Top Level
p42
ag35
aI0
aa(lp43
VVerification Review
p44
aVDate:\u000a\u000aAttendees:\u000a\u000aStandalone verification plan Hash:\u000a\u000aAPI Status:\u000a\u000aGeneral comments:\u000a
p45
aI0
aa(lp46
VGIT Status
p47
ag35
aI0
aasVrfu_dict
p48
(dp49
sVrfu_list
p50
(lp51
(V000_issue_req signals stable
p52
g1
(cvp_pack
Prop
p53
g3
Ntp54
Rp55
(dp56
Vitem_count
p57
I1
sg8
g52
sVtag
p58
VVP_IP000_P000
p59
sVitem_list
p60
(dp61
sg12
I0
sg50
(lp62
(V000
p63
g1
(cvp_pack
Item
p64
g3
Ntp65
Rp66
(dp67
g8
V000
p68
sg58
VVP_IP000_P000_I000
p69
sVdescription
p70
VThe \u201cinstr\u201d and \u201cmode\u201d signals remain stable during an Issue request transaction.
p71
sVpurpose
p72
VThis is a pointer to the source Requirements document of the Features in question.  The pointer should state the version of the target document.
p73
sVstatus
p74
g35
sVpfc
p75
I4
sVtest_type
p76
I3
sVcov_method
p77
I1
sVsimu_target_list
p78
(lp79
sg50
(lp80
sg48
(dp81
Vlock_status
p82
I0
ssVverif_goals
p83
VCheck that \u201cmode\u201d and \u201cinstr\u201d are stable during an issue transaction (cannot be modified by an instruction when transaction issue is in process)
p84
sVcomments
p85
VIn CVA6, this feature is always true.
p86
sVcoverage_loc
p87
VCG: uvm_pkg.uvm_test_top.env.cov_model.cvxif_covg.mode_covg
p88
sbtp89
asVrfu_list_1
p90
(lp91
sVrfu_list_2
p92
(lp93
sg48
(dp94
sbtp95
a(V001_mode signal value
p96
g1
(g53
g3
Ntp97
Rp98
(dp99
g57
I2
sg8
g96
sg58
VVP_IP000_P001
p100
sg60
(dp101
sg12
I1
sg50
(lp102
(V000
p103
g1
(g64
g3
Ntp104
Rp105
(dp106
g8
V000
p107
sg58
VVP_IP000_P001_I000
p108
sg70
VWhen issue transaction starts, instruction and current CPU mode are provided
p109
sg72
g35
sg74
g35
sg75
I3
sg76
I3
sg77
I1
sg78
(lp110
sg50
(lp111
sg48
(dp112
g82
I0
ssg83
VCheck that a mode modification coming from execution of a first instruction is well provided to the following offloaded instruction
p113
sg85
V For CVA6, RM is Spike.
p114
sg87
VCG: uvm_pkg.uvm_test_top.env.cov_model.cvxif_covg.mode_covg
p115
sVcores
p116
I-1
sbtp117
a(V001
p118
g1
(g64
g3
Ntp119
Rp120
(dp121
g8
V001
p122
sg58
VVP_IP000_P001_I001
p123
sg70
VCheck \u201cmode\u201d signal values
p124
sg72
g35
sg74
g35
sg75
I11
sg76
I10
sg77
I0
sg78
(lp125
sg50
(lp126
sg48
(dp127
g82
I0
ssg83
VCheck that mode take a value that the CPU supports : Privilege level (2\u2019b00 = User, 2\u2019b01 = Supervisor, 2\u2019b10 = Reserved, 2\u2019b11 = Machine).
p128
sg85
VPFC, Test Type and Coverage Method: See integration sheet.  In CVA6, this feature is always true.
p129
sg87
g35
sg116
I-1
sbtp130
asg90
(lp131
sg92
(lp132
sg48
(dp133
sbtp134
asVrfu_list_0
p135
(lp136
sg90
(lp137
sVvptool_gitrev
p138
V$Id$
p139
sbtp140
.