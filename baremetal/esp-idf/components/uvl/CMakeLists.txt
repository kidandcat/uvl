# The UVL bundle (generated Lean C + uvl_rt.c) as an ESP-IDF component.
if(NOT DEFINED UVL_BUNDLE)
  set(UVL_BUNDLE $ENV{UVL_BUNDLE})
endif()
if(NOT UVL_BUNDLE)
  message(FATAL_ERROR "Set UVL_BUNDLE to the output directory of baremetal/tools/uvl_bundle.py")
endif()
include(${UVL_BUNDLE}/uvl_bundle.cmake)

idf_component_register(SRCS ${UVL_BUNDLE_SOURCES} INCLUDE_DIRS ${UVL_BUNDLE_INCLUDE})
# Generated code is not warning-clean.
target_compile_options(${COMPONENT_LIB} PRIVATE -w)
target_compile_definitions(${COMPONENT_LIB} PRIVATE UVL_HEAP_SIZE=98304)
