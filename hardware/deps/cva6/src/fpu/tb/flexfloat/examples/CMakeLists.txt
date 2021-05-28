add_executable(example01 example01.c)
target_link_libraries(example01 PRIVATE flexfloat)
target_link_libraries(example01 PUBLIC m)

add_executable(example_stats example_stats.c)
target_link_libraries(example_stats PRIVATE flexfloat)
target_link_libraries(example_stats PUBLIC m)

add_executable(example_tracking example_tracking.c)
target_link_libraries(example_tracking PRIVATE flexfloat)
target_link_libraries(example_tracking PUBLIC m)

add_executable(example01_cpp example01.cpp)
target_link_libraries(example01_cpp PRIVATE flexfloat)
target_link_libraries(example01_cpp PUBLIC m)

