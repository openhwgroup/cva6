
# This constraints file contains default clock frequencies to be used during creation of a 
# Synthesis Design Checkpoint (DCP). For best results the frequencies should be modified 
# to match the target frequencies. 
# This constraints file is not used in top-down/global synthesis (not the default flow of Vivado).

#################
#DEFAULT CLOCK CONSTRAINTS

############################################################
# Clock Period Constraints                                 #
############################################################



#-----------------------------------------------------------
# PCS/PMA Clock period Constraints: please do not relax    -
#-----------------------------------------------------------

create_clock -name gtrefclk -period 8.000 [get_ports gtrefclk_p]


create_clock -name independent_clock_bufg -period 5.000 [get_ports independent_clock_bufg]



