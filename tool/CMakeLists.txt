cmake_minimum_required(VERSION 2.6)
project(sigrefmc C CXX)

set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/")

set(CMAKE_C_FLAGS "-O3 -Wextra -Wall -Werror -fno-strict-aliasing -std=gnu11")
set(CMAKE_CXX_FLAGS "-O3 -Wextra -Wall -Werror -fno-strict-aliasing -Wno-deprecated-register -std=gnu++11")

include_directories(sylvan/src)
add_subdirectory(sylvan/src)

include_directories(src)
add_subdirectory(src)
