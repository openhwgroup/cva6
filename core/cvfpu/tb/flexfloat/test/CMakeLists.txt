include(cmake/GoogleTest.cmake)

add_executable(conversion conversion.cpp)
target_link_libraries(conversion flexfloat gtest_main)
add_test(NAME test_conversion COMMAND conversion)

add_executable(assignment assignment.cpp)
target_link_libraries(assignment flexfloat gtest_main)
add_test(NAME test_assignment COMMAND assignment)

add_executable(sanitize sanitize.cpp)
target_link_libraries(sanitize flexfloat gtest_main)
add_test(NAME test_sanitize COMMAND sanitize)

add_executable(nearest_rounding nearest_rounding.cpp)
target_link_libraries(nearest_rounding flexfloat gtest_main)
add_test(NAME test_nearest_rounding COMMAND nearest_rounding)

add_executable(upward_rounding upward_rounding.cpp)
target_link_libraries(upward_rounding flexfloat gtest_main)
add_test(NAME test_upward_rounding COMMAND upward_rounding)

add_executable(downward_rounding downward_rounding.cpp)
target_link_libraries(downward_rounding flexfloat gtest_main)
add_test(NAME test_downward_rounding COMMAND downward_rounding)

add_executable(NanInf NanInf.cpp)
if(QUAD_BACKEND)
target_link_libraries(NanInf quadmath flexfloat gtest_main)
else()
target_link_libraries(NanInf  flexfloat gtest_main)
endif()
add_test(NAME test_NanInf COMMAND NanInf)

add_executable(rel_ops rel_ops.cpp)
target_link_libraries(rel_ops flexfloat gtest_main)
add_test(NAME test_rel_ops COMMAND rel_ops)

add_executable(arithmetic arithmetic.cpp)
target_link_libraries(arithmetic flexfloat gtest_main)
add_test(NAME test_arithmetic COMMAND arithmetic)

add_library(ieee_helper STATIC IEEEHelper.cpp)

add_executable(value_representation value_representation.cpp)
target_link_libraries(value_representation flexfloat gtest_main ieee_helper)
add_test(NAME test_value_representation COMMAND value_representation)

add_executable(value_representation_half value_representation_half.cpp)
if(QUAD_BACKEND)
target_link_libraries(value_representation_half quadmath  flexfloat gtest_main ieee_helper)
else()
target_link_libraries(value_representation_half flexfloat gtest_main ieee_helper)
endif()
add_test(NAME test_value_representation_half COMMAND value_representation_half)
