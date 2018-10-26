cmake_minimum_required(VERSION 2.6)
project(sigref C CXX)

include_directories(.)

set(SOURCES
    bisimulation.hpp
    bisim_ctmc.cpp
    bisim_lts.cpp
    bisim_lts2.cpp
    bisim_imc.cpp
    getrss.h
    getrss.c
    blocks.h
    blocks.c
    inert.h
    inert.c
    parse_bdd.hpp
    parse_bdd.cpp
    parse_xml.hpp
    parse_xml.cpp
    refine.h
    systems.hpp
    sigref.h
    sigref.cpp
    sigref_util.hpp
    sigref_util.cpp
    quotient.hpp
    quotient.cpp
    writer.hpp
    writer.cpp
    )

add_executable(sigrefmc ${SOURCES} refine_sl.c)
target_link_libraries(sigrefmc sylvan tinyxml gmp)

add_executable(sigrefmc_ht ${SOURCES} refine_ht.c)
target_link_libraries(sigrefmc_ht sylvan tinyxml gmp)

include(CheckIncludeFiles)
check_include_files("gperftools/profiler.h" HAVE_PROFILER)

find_path(HAVE_TINYXML_H tinyxml.h)

find_package(Boost REQUIRED)

if(NOT HAVE_TINYXML_H)
    message(FATAL_ERROR "tinyxml not found")
endif()

if(HAVE_PROFILER)
    set_target_properties(sigrefmc PROPERTIES COMPILE_DEFINITIONS "HAVE_PROFILER")
    target_link_libraries(sigrefmc profiler)

    set_target_properties(sigrefmc_ht PROPERTIES COMPILE_DEFINITIONS "HAVE_PROFILER")
    target_link_libraries(sigrefmc_ht profiler)
endif()

if (${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # add argp library for OSX
    target_link_libraries(sigrefmc argp)
    target_link_libraries(sigrefmc_ht argp)
endif()
