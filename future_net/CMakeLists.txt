# CMake 最低版本号要求
cmake_minimum_required(VERSION 2.8)

# 项目信息
project(future_net)

include(FindPkgConfig)
pkg_search_module(CBC REQUIRED cbc)


# include路径
include_directories(${PROJECT_SOURCE_DIR}/lib)

# 设置可执行文件生成路径
set(EXECUTABLE_OUTPUT_PATH ${PROJECT_BINARY_DIR}/../bin)

# 生成Release版本
SET(CMAKE_BUILD_TYPE "Release")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -static -Wno-sign-compare")
SET(CMAKE_CXX_FLAGS_DEBUG "$ENV{CXXFLAGS} -O0 -Wall -g -ggdb")
SET(CMAKE_CXX_FLAGS_RELEASE "$ENV{CXXFLAGS} -O3 -Wall")

# 查找当前目录下的所有源文件
# 并将名称保存到 DIR_LIB_SRCS 变量
aux_source_directory(. DIR_SRCS)

# 指定生成目标 
add_executable(future_net ${DIR_SRCS} TSPCut.hpp)
target_link_libraries(future_net ${CBC_LIBRARIES})
target_include_directories(future_net PUBLIC ${CBC_INCLUDE_DIRS})
target_compile_options(future_net PUBLIC ${CBC_CFLAGS_OTHER})
