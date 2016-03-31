cmake_minimum_required(VERSION 2.8)

project(future_net)

include_directories(${PROJECT_SOURCE_DIR}/lib)

set(EXECUTABLE_OUTPUT_PATH ${PROJECT_BINARY_DIR}/../bin)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -O3 -Wno-sign-compare -static")

aux_source_directory(. DIR_SRCS)
add_executable(future_net ${DIR_SRCS})
target_link_libraries(future_net lpsolve55 m dl colamd stdc++)
target_include_directories(future_net PUBLIC /usr/include/lpsolve)