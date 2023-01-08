/* An MSX-disk image creation/extraction program

   Copyright (C) 2004 David Heremans <dhran@pi.be>
   Copyright (C) 2005 BouKiCHi

   This program is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by the
   Free Software Foundation; either version 2, or (at your option) any later
   version.
   As a side note: Please inform me about your modifications if you make any.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General
   Public License for more details.

   You should have received a copy of the GNU General Public License along
   with this program; if not, write to the Free Software Foundation, Inc.,
   59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/

#include "StringOp.hh"
#include "endian.hh"
#include <algorithm>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <dirent.h>
#include <getopt.h>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <string_view>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <utime.h>

#define PRT_DEBUG(mes)                                                         \
	if (showDebug) {                                                       \
		std::cerr << "DEBUG: " << mes << '\n';                         \
	}

#define PRT_VERBOSE(mes)                                                       \
	if (verboseOption) {                                                   \
		std::cout << mes << '\n';                                      \
	}

#define CRITICAL_ERROR(mes)                                                    \
	std::cout << "FATAL ERROR: " << mes << '\n';                           \
	exit(1);

struct MSXBootSector {
	uint8_t jumpCode[3];           // 0xE5 to boot program
	uint8_t name[8];
	Endian::UA_L16 bpSector;       // uint8_ts per sector (always 512)
	uint8_t spCluster;             // sectors per cluster (always 2)
	Endian::UA_L16 resvSectors;    // amount of non-data sectors (ex boot sector)
	uint8_t nrFats;                // number of fats
	Endian::UA_L16 dirEntries;     // max number of files in root directory
	Endian::UA_L16 nrSectors;      // number of sectors on this disk
	uint8_t descriptor;            // media descriptor
	Endian::UA_L16 sectorsFat;     // sectors per FAT
	Endian::UA_L16 sectorsTrack;   // sectors per track
	Endian::UA_L16 nrSides;        // number of sides
	Endian::UA_L16 hiddenSectors;  // not used
	uint8_t bootProgram[512 - 30]; // actual boot program
};

struct MSXDirEntry {
	uint8_t filename[8];
	uint8_t ext[3];
	uint8_t attrib;
	uint8_t reserved[10]; // unused
	Endian::UA_L16 time;
	Endian::UA_L16 date;
	Endian::UA_L16 startCluster;
	Endian::UA_L32 size;
};

// Modified struct taken over from Linux' fdisk.h
struct Partition {
	uint8_t boot_ind;      // 0x80 - active
	uint8_t head;          // starting head
	uint8_t sector;        // starting sector
	uint8_t cyl;           // starting cylinder
	uint8_t sys_ind;       // What partition type
	uint8_t end_head;      // end head
	uint8_t end_sector;    // end sector
	uint8_t end_cyl;       // end cylinder
	Endian::UA_L32 start4; // starting sector counting from 0
	Endian::UA_L32 size4;  // nr of sectors in partition
};

struct PC98Part {
	uint8_t bootA;
	uint8_t bootB;
	uint8_t reserveA[6];
	uint8_t reserveB[2];
	uint8_t startCyl[2];
	uint8_t reserveC[2];
	uint8_t endCyl[2];
	uint8_t name[16];
};

#ifndef ACCESSPERMS
#define ACCESSPERMS 0777 // is this ok?
#endif

uint16_t EOF_FAT = 0x0FFF; // signals EOF in FAT12

int SECTOR_SIZE = 512;

static constexpr uint8_t T_MSX_REG  = 0x00; // Normal file
static constexpr uint8_t T_MSX_READ = 0x01; // Read-Only file
static constexpr uint8_t T_MSX_HID  = 0x02; // Hidden file
static constexpr uint8_t T_MSX_SYS  = 0x04; // System file
static constexpr uint8_t T_MSX_VOL  = 0x08; // filename is Volume Label
static constexpr uint8_t T_MSX_DIR  = 0x10; // entry is a subdir
static constexpr uint8_t T_MSX_ARC  = 0x20; // Archive bit

struct PhysDirEntry {
	int sector;
	uint8_t index;
};

#define NUM_OF_ENT (SECTOR_SIZE / 0x20) // number of entries in 1sector

char* programName;

long sizeOfDskFile;
uint8_t* dskImage;
uint8_t* fsImage;
std::string msxRootDir;
std::string msxHostDir;
std::string inputFile;
std::string outputFile;
int nbSectors;
int maxCluster;
int sectorsPerCluster;
int sectorsPerTrack;
int sectorsPerFat;
int nbFats;
int nbSides;
uint8_t nbSectorsPerCluster = 2;
int nbRootDirSectors;
int rootDirStart; // first sector from the root directory
int rootDirEnd;   // last sector from the root directory
int msxChrootSector;
int msxChrootStartIndex = 0;
int msxPartition = 0;
int globalArgc;
char** globalArgv;
int verboseOption = 0;
bool doTest = false; // reserved the flag for test how don't want to write to disk actually
bool doFlat = false; // reserved the flag for MSX1ers who don't like to create subdirs
bool doExtract = false;
bool doSubdirs = true;
bool doSingleSided = false;
bool touchOption = false;
bool keepOption = false;
bool msxDirOption = false;
bool msxPartOption = false;
bool msxAllPart = false;

static int showVersion = 0;  // If nonzero, display version information and exit
static int showHelp = 0;     // If nonzero, display usage information and exit
static int showDebug = 0;    // If nonzero, display debug information while running
static int showBootInfo = 0; // If nonzero, display debug information while running
static int doFat16 = 0;      // Force FAT16 support, ide >32M automatically sets this

enum { DEBUG_OPTION = CHAR_MAX + 1, OTHER_OPTION };

// boot block created with regular nms8250 and '_format'
static constexpr uint8_t dos1BootBlock[512] = {
	0xeb,0xfe,0x90,0x4e,0x4d,0x53,0x20,0x32,0x2e,0x30,0x50,0x00,0x02,0x02,0x01,0x00,
	0x02,0x70,0x00,0xa0,0x05,0xf9,0x03,0x00,0x09,0x00,0x02,0x00,0x00,0x00,0xd0,0xed,
	0x53,0x59,0xc0,0x32,0xd0,0xc0,0x36,0x56,0x23,0x36,0xc0,0x31,0x1f,0xf5,0x11,0xab,
	0xc0,0x0e,0x0f,0xcd,0x7d,0xf3,0x3c,0xca,0x63,0xc0,0x11,0x00,0x01,0x0e,0x1a,0xcd,
	0x7d,0xf3,0x21,0x01,0x00,0x22,0xb9,0xc0,0x21,0x00,0x3f,0x11,0xab,0xc0,0x0e,0x27,
	0xcd,0x7d,0xf3,0xc3,0x00,0x01,0x58,0xc0,0xcd,0x00,0x00,0x79,0xe6,0xfe,0xfe,0x02,
	0xc2,0x6a,0xc0,0x3a,0xd0,0xc0,0xa7,0xca,0x22,0x40,0x11,0x85,0xc0,0xcd,0x77,0xc0,
	0x0e,0x07,0xcd,0x7d,0xf3,0x18,0xb4,0x1a,0xb7,0xc8,0xd5,0x5f,0x0e,0x06,0xcd,0x7d,
	0xf3,0xd1,0x13,0x18,0xf2,0x42,0x6f,0x6f,0x74,0x20,0x65,0x72,0x72,0x6f,0x72,0x0d,
	0x0a,0x50,0x72,0x65,0x73,0x73,0x20,0x61,0x6e,0x79,0x20,0x6b,0x65,0x79,0x20,0x66,
	0x6f,0x72,0x20,0x72,0x65,0x74,0x72,0x79,0x0d,0x0a,0x00,0x00,0x4d,0x53,0x58,0x44,
	0x4f,0x53,0x20,0x20,0x53,0x59,0x53,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
};

// boot block created with nms8250 and MSX-DOS 2.20
static constexpr uint8_t dos2BootBlock[512] = {
	0xeb,0xfe,0x90,0x4e,0x4d,0x53,0x20,0x32,0x2e,0x30,0x50,0x00,0x02,0x02,0x01,0x00,
	0x02,0x70,0x00,0xa0,0x05,0xf9,0x03,0x00,0x09,0x00,0x02,0x00,0x00,0x00,0x18,0x10,
	0x56,0x4f,0x4c,0x5f,0x49,0x44,0x00,0x71,0x60,0x03,0x19,0x00,0x00,0x00,0x00,0x00,
	0xd0,0xed,0x53,0x6a,0xc0,0x32,0x72,0xc0,0x36,0x67,0x23,0x36,0xc0,0x31,0x1f,0xf5,
	0x11,0xab,0xc0,0x0e,0x0f,0xcd,0x7d,0xf3,0x3c,0x28,0x26,0x11,0x00,0x01,0x0e,0x1a,
	0xcd,0x7d,0xf3,0x21,0x01,0x00,0x22,0xb9,0xc0,0x21,0x00,0x3f,0x11,0xab,0xc0,0x0e,
	0x27,0xcd,0x7d,0xf3,0xc3,0x00,0x01,0x69,0xc0,0xcd,0x00,0x00,0x79,0xe6,0xfe,0xd6,
	0x02,0xf6,0x00,0xca,0x22,0x40,0x11,0x85,0xc0,0x0e,0x09,0xcd,0x7d,0xf3,0x0e,0x07,
	0xcd,0x7d,0xf3,0x18,0xb8,0x42,0x6f,0x6f,0x74,0x20,0x65,0x72,0x72,0x6f,0x72,0x0d,
	0x0a,0x50,0x72,0x65,0x73,0x73,0x20,0x61,0x6e,0x79,0x20,0x6b,0x65,0x79,0x20,0x66,
	0x6f,0x72,0x20,0x72,0x65,0x74,0x72,0x79,0x0d,0x0a,0x24,0x00,0x4d,0x53,0x58,0x44,
	0x4f,0x53,0x20,0x20,0x53,0x59,0x53,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
};

const uint8_t* defaultBootBlock = dos2BootBlock;

uint16_t getLE16(const uint8_t* x)
{
	return (x[0] << 0) + (x[1] << 8);
}

/** Transforms a cluster number towards the first sector of this cluster
 * The calculation uses info read fom the boot sector
 */
int clusterToSector(int cluster)
{
	return 1 + rootDirEnd + sectorsPerCluster * (cluster - 2);
}

/** Transforms a sector number towards it containing cluster
 * The calculation uses info read fom the boot sector
 */
uint16_t sectorToCluster(int sector)
{
	return 2 + (int)((sector - (1 + rootDirEnd)) / sectorsPerCluster);
}

/** Initialize global variables by reading info from the boot sector
 */
void readBootSector()
{
	MSXBootSector* boot = (MSXBootSector*)fsImage;

	nbSectors = boot->nrSectors; // assume a DS disk is used
	SECTOR_SIZE = boot->bpSector;
	sectorsPerTrack = boot->sectorsTrack;
	nbSides = boot->nrSides;
	nbFats = boot->nrFats;
	sectorsPerFat = boot->sectorsFat;
	nbRootDirSectors = boot->dirEntries / (SECTOR_SIZE / 32);
	sectorsPerCluster = boot->spCluster;

	rootDirStart = 1 + nbFats * sectorsPerFat;
	msxChrootSector = rootDirStart;

	rootDirEnd = rootDirStart + nbRootDirSectors - 1;
	maxCluster = sectorToCluster(nbSectors);

	if (showBootInfo) {
		std::cout << "---------- Boot sector info -----\n"
		             "\n"
		             "  bytes per sector:      " << boot->bpSector << "\n"
		             "  sectors per cluster:   " << int(boot->spCluster) << "\n"
		             "  number of FAT's:       " << int(boot->nrFats) << "\n"
		             "  dirEntries in rootDir: " << boot->dirEntries << "\n"
		             "  sectors on disk:       " << boot->nrSectors << "\n"
		             "  media descriptor:      " << std::hex << int(boot->descriptor) << std::dec << "\n"
		             "  sectors per FAT:       " << boot->sectorsFat << "\n"
		             "  sectors per track:     " << boot->sectorsTrack << "\n"
		             "  number of sides:       " << boot->nrSides << "\n"
		             "\n"
		             "Calculated values\n"
		             "\n"
		             "maxCluster   " << maxCluster << "\n"
		             "RootDirStart " << rootDirStart << "\n"
		             "RootDirEnd   " << rootDirEnd << "\n"
		             "---------------------------------\n"
		             "\n";
	}
}

/** Create a correct boot sector depending on the required size of the filesystem
 * Will implicitly call readBootSector for global var initialising
 */
void setBootSector(uint16_t nbSectors)
{
	// variables set to single sided disk by default
	uint16_t nbSides = 1;
	uint8_t nbFats = 2;
	uint8_t nbReservedSectors = 1; // Just copied from a 32MB IDE partition
	uint8_t nbSectorsPerFat = 2;
	uint8_t nbHiddenSectors = 1;
	uint16_t nbDirEntry = 112;
	uint8_t descriptor = 0xf8;

	// now set correct info according to size of image (in sectors!)
	// and using the same layout as used by Jon in IDEFDISK v 3.1
	if (nbSectors >= 32733) {
		nbSides = 2; // unknown yet
		nbFats = 2;  // unknown yet
		nbSectorsPerFat = 12; // copied from a partition from an IDE HD
		nbSectorsPerCluster = 16;
		nbDirEntry = 256;
		nbSides = 32; // copied from a partition from an IDE HD
		nbHiddenSectors = 16;
		descriptor = 0xf0;
	} else if (nbSectors >= 16389) {
		nbSides = 2;         // unknown yet
		nbFats = 2;          // unknown yet
		nbSectorsPerFat = 3; // unknown yet
		nbSectorsPerCluster = 8;
		nbDirEntry = 256;
		descriptor = 0xf0;
	} else if (nbSectors >= 8213) {
		nbSides = 2;         // unknown yet
		nbFats = 2;          // unknown yet
		nbSectorsPerFat = 3; // unknown yet
		nbSectorsPerCluster = 4;
		nbDirEntry = 256;
		descriptor = 0xf0;
	} else if (nbSectors >= 4127) {
		nbSides = 2;         // unknown yet
		nbFats = 2;          // unknown yet
		nbSectorsPerFat = 3; // unknown yet
		nbSectorsPerCluster = 2;
		nbDirEntry = 256;
		descriptor = 0xf0;
	} else if (nbSectors >= 2880) {
		nbSides = 2;         // unknown yet
		nbFats = 2;          // unknown yet
		nbSectorsPerFat = 3; // unknown yet
		nbSectorsPerCluster = 1;
		nbDirEntry = 224;
		descriptor = 0xf0;
	} else if (nbSectors >= 1441) {
		nbSides = 2;         // unknown yet
		nbFats = 2;          // unknown yet
		nbSectorsPerFat = 3; // unknown yet
		nbSectorsPerCluster = 2;
		nbDirEntry = 112;
		descriptor = 0xf0;
	} else if (nbSectors <= 720) {
		// normal single sided disk
		nbSectors = 720;
	} else {
		// normal double sided disk
		nbSectors = 1440;
		nbSides = 2;
		nbFats = 2;
		nbSectorsPerFat = 3;
		nbSectorsPerCluster = 2;
		nbDirEntry = 112;
		descriptor = 0xf9;
	}
	MSXBootSector* boot = (MSXBootSector*)fsImage;

	boot->nrSectors = nbSectors;
	boot->nrSides = nbSides;
	boot->spCluster = (uint8_t)nbSectorsPerCluster;
	boot->nrFats = nbFats;
	boot->sectorsFat = nbSectorsPerFat;
	boot->dirEntries = nbDirEntry;
	boot->descriptor = descriptor;
	boot->resvSectors = nbReservedSectors;
	boot->hiddenSectors = nbHiddenSectors;

	readBootSector();
}

// Get the next cluster number from the FAT chain
uint16_t readFAT(uint16_t clNr)
{
	if (!doFat16) {
		const uint8_t* p = fsImage + SECTOR_SIZE + (clNr * 3) / 2;
		return (clNr & 1) ? (p[0] >> 4) + (p[1] << 4)
		                  : p[0] + ((p[1] & 0x0F) << 8);
	} else {
		std::cout << "FAT size 16 not yet tested!!\n";
		const uint8_t* p = fsImage + SECTOR_SIZE + (clNr * 2);
		return p[0] + (p[1] << 8);
	}
}

// Write an entry to the FAT
void writeFAT(uint16_t clNr, uint16_t val)
{
	if (!doFat16) {
		uint8_t* p = fsImage + SECTOR_SIZE + (clNr * 3) / 2;
		if (clNr & 1) {
			p[0] = (p[0] & 0x0F) + (val << 4);
			p[1] = val >> 4;
		} else {
			p[0] = val;
			p[1] = (p[1] & 0xF0) + ((val >> 8) & 0x0F);
		}
	} else {
		std::cout << "FAT size 16 not yet tested!!\n";
		uint8_t* p = fsImage + SECTOR_SIZE + (clNr * 2);
		p[0] = val & 0xFF;
		p[1] = (val >> 8) & 0xFF;
	}
}

// Find the next cluster number marked as free in the FAT
uint16_t findFirstFreeCluster()
{
	int cluster = 2;
	while ((cluster <= maxCluster) && readFAT(cluster)) {
		++cluster;
	}
	return cluster;
}

void mkdir_ex(const char* name, mode_t perm)
{
#ifdef __WIN32__
	mkdir(name);
#else
	mkdir(name, perm);
#endif
}

/** Returns the index of a free (or with deleted file) entry
 * in the current dir sector
 * Out: index (is max 15), if no index is found then 16 is returned
 */
uint8_t findUsableIndexInSector(int sector)
{
	// find a not used (0x00) or deleted entry (0xe5)
	uint8_t* p = fsImage + SECTOR_SIZE * sector;
	uint8_t i = 0;
	while (i < NUM_OF_ENT && p[0] != 0x00 && p[0] != 0xe5) {
		++i;
		p += 32;
	}
	return i;
}

/** Get the next sector from a file or (sub)directory
 * If no next sector then 0 is returned
 */
int getNextSector(int sector)
{
	// if this sector is part of the root directory...
	if (sector == rootDirEnd) return 0;
	if (sector < rootDirEnd) return sector + 1;

	if ((nbSectorsPerCluster > 1) &&
	    (sectorToCluster(sector) == sectorToCluster(sector + 1))) {
		return sector + 1;
	} else {
		int nextCl = readFAT(sectorToCluster(sector));
		if (nextCl == EOF_FAT) {
			return 0;
		} else {
			return clusterToSector(nextCl);
		}
	}
}

/** if there are no more free entries in a subdirectory, the subdir is
 * expanded with an extra cluster, This function gets the free cluster,
 * clears it and updates the fat for the subdir
 * returns: the first sector in the newly appended cluster, or 0 in case of error
 */
int appendClusterToSubdir(int sector)
{
	uint16_t curCl = sectorToCluster(sector);
	if (readFAT(curCl) != EOF_FAT) {
		CRITICAL_ERROR("appendClusterToSubdir called with sector in a not EOF_FAT cluster");
	}
	uint16_t nextCl = findFirstFreeCluster();
	if (nextCl > maxCluster) {
		std::cout << "Disk full no more free clusters\n";
		return 0;
	}
	int logicalSector = clusterToSector(nextCl);
	// clear this cluster
	memset(fsImage + SECTOR_SIZE * logicalSector, 0, SECTOR_SIZE * sectorsPerCluster);
	writeFAT(curCl, nextCl);
	writeFAT(nextCl, EOF_FAT);
	return logicalSector;
}
/** Find the dir entry for 'name' in subdir starting at the given 'sector'
 * with given 'index'
 * returns: a pointer to a MSXDirEntry if name was found
 *          a nullptr if no match was found
 */
MSXDirEntry* findEntryInDir(const std::string& name, int sector, uint8_t dirEntryIndex)
{
	uint8_t* p = fsImage + SECTOR_SIZE * sector + 32 * dirEntryIndex;
	uint8_t i = 0;
	do {
		i = 0;
		while (i < NUM_OF_ENT && strncmp(name.c_str(), (char*)p, 11) != 0) {
			++i;
			p += 32;
		}
		if (i == NUM_OF_ENT) {
			sector = getNextSector(sector);
			p = fsImage + SECTOR_SIZE * sector;
		}
	} while (i >= NUM_OF_ENT && sector);
	return sector ? (MSXDirEntry*)p : nullptr;
}

/** This function returns the sector and dirIndex for a new directory entry
 * if needed the involved subdirectory is expanded by an extra cluster
 * returns: a PhysDirEntry containing sector and index
 *          if failed then the sector number is 0
 */
PhysDirEntry addEntryToDir(int sector)
{
	// this routine adds the msxName to a directory sector, if needed (and
	// possible) the directory is extened with an extra cluster
	PhysDirEntry newEntry;
	uint8_t newIndex = findUsableIndexInSector(sector);
	if (sector <= rootDirEnd) {
		// we are adding this to the root sector
		while (newIndex >= NUM_OF_ENT && sector <= rootDirEnd) {
			newIndex = findUsableIndexInSector(++sector);
		}
		newEntry.sector = sector;
		newEntry.index = newIndex;
	} else {
		// we are adding this to a subdir
		if (newIndex < NUM_OF_ENT) {
			newEntry.sector = sector;
			newEntry.index = newIndex;
		} else {
			while (newIndex >= NUM_OF_ENT && sector != 0) {
				int nextSector = getNextSector(sector);
				if (nextSector == 0) {
					nextSector = appendClusterToSubdir(sector);
					PRT_DEBUG("appendClusterToSubdir(" << sector << ") returns" << nextSector);
					if (nextSector == 0) {
						CRITICAL_ERROR("disk is full");
					}
				}
				sector = nextSector;
				newIndex = findUsableIndexInSector(sector);
			}
			newEntry.sector = sector;
			newEntry.index = newIndex;
			//CRITICAL_ERROR("subdir needs more than 16 entries");
		}
	}
	return newEntry;
}

// create an MSX filename 8.3 format, if needed in vfat like abbreviation
static char toMSXChr(char a)
{
	a = toupper(a);
	if (a == ' ' || a == '.') {
		a = '_';
	}
	return a;
}

/** Transform a long hostname in a 8.3 uppercase filename as used in the
 * dirEntries on an MSX
 */
std::string makeSimpleMSXFileName(std::string_view fullFilename)
{
	auto [dir, fullFile] = StringOp::splitOnLast(fullFilename, "/\\");

	// handle special case '.' and '..' first
	std::string result(8 + 3, ' ');
	if (fullFile == "." || fullFile == "..") {
		memcpy(result.data(), fullFile.data(), fullFile.size());
		return result;
	}

	auto [file, ext] = StringOp::splitOnLast(fullFile, '.');
	if (file.empty()) std::swap(file, ext);

	StringOp::trimRight(file, ' ');
	StringOp::trimRight(ext , ' ');

	// put in major case and create '_' if needed
	std::string fileS(file.data(), std::min<size_t>(8, file.size()));
	std::string extS (ext .data(), std::min<size_t>(3, ext .size()));
	transform(fileS.begin(), fileS.end(), fileS.begin(), toMSXChr);
	transform(extS .begin(), extS .end(), extS .begin(), toMSXChr);

	// add correct number of spaces
	memcpy(result.data() + 0, fileS.data(), fileS.size());
	memcpy(result.data() + 8, extS .data(), extS .size());
	return result;
}

/** This function creates a new MSX subdir with given date 'd' and time 't'
 * in the subdir pointed at by 'sector' in the newly
 * created subdir the entries for '.' and '..' are created
 * returns: the first sector of the new subdir
 *          0 in case no directory could be created
 */
int addMSXSubdir(const std::string& msxName, int t, int d, int sector)
{
	// returns the sector for the first cluster of this subdir
	PhysDirEntry result = addEntryToDir(sector);
	if (result.index >= NUM_OF_ENT) {
		std::cout << "couldn't add entry" << msxName << '\n';
		return 0;
	}
	MSXDirEntry* dirEntry =
	        (MSXDirEntry*)(fsImage + SECTOR_SIZE * result.sector + 32 * result.index);
	dirEntry->attrib = T_MSX_DIR;
	dirEntry->time = t;
	dirEntry->date = d;
	memcpy(dirEntry, makeSimpleMSXFileName(msxName).c_str(), 11);

	// dirEntry->fileSize = fSize;
	uint16_t curCl = 2;
	curCl = findFirstFreeCluster();
	PRT_DEBUG("New subdir starting at cluster " << curCl);
	dirEntry->startCluster = curCl;
	writeFAT(curCl, EOF_FAT);
	int logicalSector = clusterToSector(curCl);
	// clear this cluster
	memset(fsImage + SECTOR_SIZE * logicalSector, 0, SECTOR_SIZE * sectorsPerCluster);
	// now add the '.' and '..' entries!!
	dirEntry = (MSXDirEntry*)(fsImage + SECTOR_SIZE * logicalSector);
	memset(dirEntry, 0, sizeof(MSXDirEntry));
	memset(dirEntry, 0x20, 11); // all spaces
	memset(dirEntry, '.', 1);
	dirEntry->attrib = T_MSX_DIR;
	dirEntry->time = t;
	dirEntry->date = d;
	dirEntry->startCluster = curCl;

	++dirEntry;
	memset(dirEntry, 0, sizeof(MSXDirEntry));
	memset(dirEntry, 0x20, 11); // all spaces
	memset(dirEntry, '.', 2);
	dirEntry->attrib = T_MSX_DIR;
	dirEntry->time = t;
	dirEntry->date = d;

	int parentCluster = sectorToCluster(sector);
	if (sector == rootDirStart) parentCluster = 0;

	dirEntry->startCluster = parentCluster;

	return logicalSector;
}

void makeFatTime(const struct tm mtim, int* dt)
{
	dt[0] = (mtim.tm_sec >> 1) + (mtim.tm_min << 5) + (mtim.tm_hour << 11);
	dt[1] = mtim.tm_mday + ((mtim.tm_mon + 1) << 5) + ((mtim.tm_year + 1900 - 1980) << 9);
}

/** Add an MSXsubdir with the time properties from the HOST-OS subdir
 */
int addSubDirToDSK(const std::string& hostName, const std::string& msxName, int sector)
{
	// compute time/date stamps
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(hostName.c_str(), &fst);
	struct tm mtim = *localtime(&(fst.st_mtime));

	int td[2];
	makeFatTime(mtim, td);

	return addMSXSubdir(msxName, td[0], td[1], sector);
}

/** This file alters the filecontent of a given file
 * It only changes the file content (and the filesize in the msxDirEntry)
 * It doesn't changes timestamps nor filename, filetype etc.
 * Output: nothing useful yet
 */
void alterFileInDSK(MSXDirEntry* msxDirEntry, const std::string& hostName)
{
	bool needsNew = false;
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(hostName.c_str(), &fst);
	int fSize = fst.st_size;

	PRT_DEBUG("AlterFileInDSK: filesize " << fSize);

	uint16_t curCl = msxDirEntry->startCluster;
	// if entry first used then no cluster assigned yet
	if (curCl == 0) {
		curCl = findFirstFreeCluster();
		msxDirEntry->startCluster = curCl;
		writeFAT(curCl, EOF_FAT);
		needsNew = true;
	}
	PRT_DEBUG("AlterFileInDSK: starting at cluster " << curCl);

	int size = fSize;
	int prevCl = 0;
	// open file for reading
	FILE* file = fopen(hostName.c_str(), "rb");

	while (file && size && (curCl <= maxCluster)) {
		int logicalSector = clusterToSector(curCl);
		uint8_t* buf = fsImage + logicalSector * SECTOR_SIZE;
		for (int j = 0; (j < sectorsPerCluster) && size; ++j) {
			PRT_DEBUG("AlterFileInDSK: relative sector " << j << " in cluster " << curCl);
			size_t chunkSize = std::min(size, SECTOR_SIZE);
			if (fread(buf, 1, chunkSize, file) != chunkSize) {
				CRITICAL_ERROR("Error while reading from " << hostName);
			}
			buf += SECTOR_SIZE;
			size -= chunkSize;
		}

		if (prevCl) {
			writeFAT(prevCl, curCl);
		}
		prevCl = curCl;
		// now we check if we continue in the current cluster string or
		// need to allocate extra unused blocks do {
		if (needsNew) {
			// need extra space for this file
			writeFAT(curCl, EOF_FAT);
			curCl = findFirstFreeCluster();
		} else {
			// follow cluster-Fat-stream
			curCl = readFAT(curCl);
			if (curCl == EOF_FAT) {
				curCl = findFirstFreeCluster();
				needsNew = true;
			}
		}
		//} while((curCl <= maxCluster) && ReadFAT(curCl));
		PRT_DEBUG("AlterFileInDSK: continuing at cluster " << curCl);
	}
	if (file) fclose(file);

	if ((size == 0) && (curCl <= maxCluster)) {
		// TODO: check what an MSX does with filesize zero and fat allocation
		if (prevCl == 0) {
			prevCl = curCl;
			curCl = readFAT(curCl);
		}
		writeFAT(prevCl, EOF_FAT);
		PRT_DEBUG("AlterFileInDSK: ending at cluster " << prevCl);
		// cleaning rest of FAT chain if needed
		while (!needsNew) {
			prevCl = curCl;
			if (curCl != EOF_FAT) {
				curCl = readFAT(curCl);
			} else {
				needsNew = true;
			}
			PRT_DEBUG("AlterFileInDSK: cleaning cluster " << prevCl << " from FAT");
			writeFAT(prevCl, 0);
		}
	} else {
		// TODO: don't we need a EOF_FAT in this case as well ?
		//  find out and adjust code here
		std::cout << "Fake disk image full: " << hostName << " truncated.\n";
	}
	// write (possibly truncated) file size
	msxDirEntry->size = fSize - size;
}

/** Add file to the MSX disk in the subdir pointed to by 'sector'
 * returns: nothing useful yet :-)
 */
void addFileToDSK(const std::string& fullHostName, int sector, uint8_t dirEntryIndex)
{
	auto [directory, hostName] = StringOp::splitOnLast(fullHostName, "/\\");
	std::string msxName = makeSimpleMSXFileName(hostName);

	// first find out if the filename already exists current dir
	if (findEntryInDir(msxName, sector, dirEntryIndex)) {
		PRT_VERBOSE("Preserving entry " << fullHostName);
		return;
	}
	PhysDirEntry result = addEntryToDir(sector);
	if (result.index >= NUM_OF_ENT) {
		std::cout << "couldn't add entry" << fullHostName << '\n';
		return;
	}
	MSXDirEntry* dirEntry =
	        (MSXDirEntry*)(fsImage + SECTOR_SIZE * result.sector + 32 * result.index);
	dirEntry->attrib = T_MSX_REG;

	dirEntry->startCluster = 0;

	PRT_VERBOSE(fullHostName << " \t-> \"" << msxName << '"');
	memcpy(dirEntry, msxName.c_str(), 11);

	// compute time/date stamps
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(fullHostName.c_str(), &fst);
	struct tm mtim = *localtime(&(fst.st_mtime));
	int td[2];

	makeFatTime(mtim, td);
	dirEntry->time = td[0];
	dirEntry->date = td[1];

	alterFileInDSK(dirEntry, fullHostName);
}

int checkStat(const std::string& name)
{
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(name.c_str(), &fst);

	if (fst.st_mode & S_IFDIR) return 0; // it's a directory

	return 1; // if it's a file
}

/** transfer directory and all its subdirectories to the MSX disk image
 */
void recurseDirFill(const std::string& dirName, int sector, int dirEntryIndex)
{
	PRT_DEBUG("Trying to read directory " << dirName);

	DIR* dir = opendir(dirName.c_str());
	if (!dir) {
		PRT_DEBUG("Not a FDC_DirAsDSK image");
		// throw MSXException("Not a directory");
	}
	// read directory and fill the fake disk
	struct dirent* d = readdir(dir);
	while (d) {
		std::string name(d->d_name);
		PRT_DEBUG("reading name in dir: " << name);
		std::string path = dirName + '/' + name;
		if (checkStat(path)) { // true if a file
			if (name.starts_with('.')) {
				std::cout << name << ": ignored file which starts with a '.'\n";
			} else {
				addFileToDSK(path, sector, dirEntryIndex); // used here to add file into fake dsk
			}
		} else if (name != "." && name != "..") {
			if (doSubdirs) {
				std::string msxName = makeSimpleMSXFileName(name);
				PRT_VERBOSE(path << " \t-> \"" << msxName << '"');
				int result;
				if (auto* msxDirEntry = findEntryInDir(msxName, sector, dirEntryIndex)) {
					PRT_VERBOSE("Dir entry " << name << " exists already");
					result = clusterToSector(msxDirEntry->startCluster);
				} else {
					PRT_VERBOSE("Adding dir entry " << name);
					result = addSubDirToDSK(path, name, sector); // used here to add file into fake dsk
				}
				recurseDirFill(path, result, 0);
			} else {
				PRT_DEBUG("Skipping subdir: " << path);
			}
		}
		d = readdir(dir);
	}
	closedir(dir);
}

/** Save the disk image from memory to disk
 */
void writeImageToDisk(const std::string& filename)
{
	if (doTest) {
		PRT_VERBOSE("MSXtar doesn't write to disk for test");
		return; // test is not to write.
	}

	FILE* file = fopen(filename.c_str(), "wb");
	if (!file) {
		std::cout << "Couldn't open file for writing!\n";
		return;
	}
	if (sizeOfDskFile) {
		fwrite(dskImage, 1, sizeOfDskFile, file);
	} else {
		fwrite(dskImage, 1, nbSectors * SECTOR_SIZE, file);
	}
	fclose(file);
}

void updateCreateDSK(const std::string& fileName)
{
	std::string msxName = makeSimpleMSXFileName(fileName);

	PRT_DEBUG("trying to stat: " << fileName);
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(fileName.c_str(), &fst);

	if (fst.st_mode & S_IFDIR) {
		// this should be a directory
		if (doFlat || !doSubdirs) {
			// put files in the directory to root
			recurseDirFill(fileName, msxChrootSector, msxChrootStartIndex);
		} else {
			PRT_VERBOSE("./" << fileName << " \t-> \"" << msxName << '"');
			int result;
			if (auto* msxDirEntry = findEntryInDir(msxName, msxChrootSector, msxChrootStartIndex)) {
				PRT_VERBOSE("Dir entry " << fileName << " exists already");
				result = clusterToSector(msxDirEntry->startCluster);
			} else {
				PRT_VERBOSE("Adding dir entry " << fileName);
				result = addSubDirToDSK(fileName, fileName, msxChrootSector);
				// used here to add file into fake dsk
			}
			recurseDirFill(fileName, result, 0);
		}
	} else {
		// this should be a normal file
		PRT_VERBOSE("Updating file " << fileName);
		// addFileToDSK(fileName, MSXchrootSector, MSXchrootStartIndex); // used here to add file into fake dsk in root dir!!
		// first find out if the filename already exists current dir
		MSXDirEntry* msxDirEntry = findEntryInDir(msxName, msxChrootSector, msxChrootStartIndex);
		alterFileInDSK(msxDirEntry, fileName);
	}
}

void addCreateDSK(const std::string& fileName)
{
	// Here we create the fake disk images based upon the files that can be
	// found in the 'fileName' directory or the single file
	PRT_DEBUG("addCreateDSK(" << fileName << ");");
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(fileName.c_str(), &fst);

	if (fst.st_mode & S_IFDIR) {
		// this should be a directory
		PRT_VERBOSE("addCreateDSK: adding directory " << fileName);

		if (doFlat || !doSubdirs) {
			// put files in the directory to root
			msxRootDir = fileName;
			recurseDirFill(fileName, msxChrootSector, msxChrootStartIndex);
		} else {
			std::string msxName = makeSimpleMSXFileName(fileName);
			PRT_VERBOSE("./" << fileName << " \t-> \"" << msxName << '"');
			int result;
			if (auto* msxDirEntry = findEntryInDir(msxName, msxChrootSector, msxChrootStartIndex)) {
				PRT_VERBOSE("Dir entry " << fileName << " exists already ");
				result = clusterToSector(msxDirEntry->startCluster);
			} else {
				PRT_VERBOSE("Adding dir entry " << fileName);
				result = addSubDirToDSK(fileName, fileName, msxChrootSector);
				// used here to add file into fake dsk
			}
			recurseDirFill(fileName, result, 0);
		}
	} else {
		// this should be a normal file
		PRT_VERBOSE("Adding file " << fileName);
		addFileToDSK(fileName, msxChrootSector, msxChrootStartIndex); // used here to add file into fake dsk in root dir!!
	}
}

void updateInDSK(std::string name)
{
	StringOp::trimRight(name, "/\\");

	// first find the filename in the current 'root dir'
	if (findEntryInDir(makeSimpleMSXFileName(name), rootDirStart, 0)) {
		if (keepOption) {
			PRT_VERBOSE("Preserving entry " << name);
		} else {
			updateCreateDSK(name);
		}
	} else {
		PRT_VERBOSE("Couldn't find entry " << name <<
		            " to update, trying to create new entry");
		addCreateDSK(name);
	}
}

/** Create an empty disk image with correct boot sector,FAT etc.
 */
void createEmptyDSK()
{
	// First create structure for the fake disk
	// Allocate dskImage in memory
	dskImage = new uint8_t[nbSectors * SECTOR_SIZE];
	fsImage = dskImage;
	if (!dskImage) {
		CRITICAL_ERROR("Not enough memory for disk image");
	}

	// Assign default boot disk to this instance
	// give extra info on the boot sector
	// and get global parameters from them (implicit readBootSector)
	memcpy(fsImage, defaultBootBlock, SECTOR_SIZE);
	setBootSector(nbSectors);

	// Assign default empty values to disk
	memset(fsImage + SECTOR_SIZE, 0x00, rootDirEnd * SECTOR_SIZE);
	memset(fsImage + ((1 + rootDirEnd) * SECTOR_SIZE), 0xE5,
	       (nbSectors - (1 + rootDirEnd)) * SECTOR_SIZE);
	// for some reason the first 3uint8_ts are used to indicate the end of a
	// cluster, making the first available cluster nr 2 some sources say
	// that this indicates the disk format and FAT[0]should 0xF7 for single
	// sided disk, and 0xF9 for double sided disks
	// TODO: check this :-)
	// for now I simply repeat the media descriptor here
	{
		MSXBootSector* boot = (MSXBootSector*)fsImage;
		fsImage[SECTOR_SIZE + 0] = boot->descriptor;
	}
	fsImage[SECTOR_SIZE + 1] = 0xFF;
	fsImage[SECTOR_SIZE + 2] = 0xFF;
}

std::string condenseName(MSXDirEntry* dirEntry)
{
	char condensedName[8 + 1 + 3 + 1];
	char* p = condensedName;
	for (int i = 0; i < 8; ++i) {
		if (dirEntry->filename[i] == ' ') {
			i = 9;
		} else {
			*(p++) = tolower(dirEntry->filename[i]);
		}
	}
	if (dirEntry->ext[0] != ' ' || dirEntry->ext[1] != ' ' || dirEntry->ext[2] != ' ') {
		*(p++) = '.';
		for (int i = 0; i < 3; ++i) {
			*p = tolower(dirEntry->ext[i]);
			if (*p == ' ') *p = (char)0;
			++p;
		}
	}
	*p = (char)0;
	return condensedName;
}

/**routine to make FSImage point to the correct part of dskImage
 * returns: true if successful, false if partition isn't valid
 */
bool chPart(int chPartition)
{
	if (strncmp((char*)dskImage, "T98HDDIMAGE.R0", 14) == 0) {
		// 0x110 size of the header(long), cylinder(long),
		// surface(uint16_t), sector(uint16_t), secsize(uint16_t)
		PRT_DEBUG("T98header recognized");
		int surf = getLE16(dskImage + 0x110 + 8);
		int sec = getLE16(dskImage + 0x110 + 10);
		int sSize = getLE16(dskImage + 0x110 + 12);

		SECTOR_SIZE = sSize;

		PC98Part* P98 = (PC98Part*)(dskImage + 0x400 + (chPartition * 16));
		int sCyl = getLE16(P98->startCyl);

		fsImage = dskImage + 0x200 + (sSize * sCyl * surf * sec);
		readBootSector();
		return true;
	}

	if (strncmp((char*)dskImage, "\353\376\220MSX_IDE ", 11) != 0) {
		std::cout << "Not an idefdisk compatible 0 sector\n";
		return false;
	}
	Partition* p = (Partition*)(dskImage + 14 + (30 - chPartition) * 16);
	if (p->start4 == 0) {
		return false;
	}
	fsImage = dskImage + SECTOR_SIZE * p->start4;
	readBootSector();
	return true;
}

/** Routine to get the first sector of a given dir name
 * input: correctly MSXformatted subdirectory name
 * returns: 0 if given directory not found
 */
int findStartSectorOfDir(std::string_view dirName)
{
	std::string_view work = dirName;
	std::string totalPath = ".";
	int msxDirSector = msxChrootSector;
	int msxDirStartIndex = msxChrootStartIndex;
	// if (!msxDirOption){return;}
	while (!work.empty()) {
		StringOp::trimLeft(work, "/\\");
		auto [directory, rest] = StringOp::splitOnFirst(work, "/\\");
		work = rest;
		// find directory
		std::string simple = makeSimpleMSXFileName(directory);
		if (auto* msxDirEntry = findEntryInDir(simple, msxDirSector, msxDirStartIndex)) {
			msxDirSector = clusterToSector(msxDirEntry->startCluster);
			msxDirStartIndex = 2;
			totalPath += '/';
			totalPath += directory;
			mkdir_ex(totalPath.c_str(), ACCESSPERMS);
		} else {
			PRT_VERBOSE("Couldn't find directory: " << dirName);
			return 0;
		}
	}
	return msxDirSector;
}

// routine to update the global vars: MSXchrootSector, MSXchrootStartIndex
void chroot(std::string_view newRootDir)
{
	if (newRootDir.starts_with('/') || newRootDir.starts_with('\\')) {
		// absolute path, reset msxChrootSector
		msxChrootSector = rootDirStart;
		StringOp::trimLeft(newRootDir, "/\\");
	}

	while (!newRootDir.empty()) {
		auto [firstPart, lastPart] = StringOp::splitOnFirst(newRootDir, "/\\");
		newRootDir = lastPart;
		StringOp::trimLeft(newRootDir, "/\\");

		// find firstPart directory or create it
		std::string simple = makeSimpleMSXFileName(firstPart);
		if (auto* msxDirEntry = findEntryInDir(simple, msxChrootSector, msxChrootStartIndex)) {
			msxChrootSector = clusterToSector(msxDirEntry->startCluster);
			msxChrootStartIndex = 2;
		} else {
			// creat new subdir
			time_t now;
			time(&now);
			struct tm mtim = *localtime(&now);
			int td[2];
			makeFatTime(mtim, td);

			std::cout << "Create subdir\n";
			msxChrootSector = addMSXSubdir(simple, td[0], td[1], msxChrootSector);
			msxChrootStartIndex = 2;
			if (msxChrootSector == 0) {
				exit(0);
			}
		}
	}
}

void makeTimeFromDE(struct tm* ptm, const int* td)
{
	ptm->tm_sec  = (td[0] & 0x1f) << 1;
	ptm->tm_min  = (td[0] & 0x03e0) >> 5;
	ptm->tm_hour = (td[0] & 0xf800) >> 11;
	ptm->tm_mday = (td[1] & 0x1f);
	ptm->tm_mon  = (td[1] & 0x01e0) >> 5;
	ptm->tm_year = ((td[1] & 0xfe00) >> 9) + 80;
}

/** Set the entries from dirEntry to the timestamp of resultFile
 */
void changeTime(const std::string& resultFile, MSXDirEntry* dirEntry)
{
	if (touchOption) return;

	int td[2];
	td[0] = dirEntry->time;
	td[1] = dirEntry->date;

	struct tm mTim;
	struct utimbuf uTim;
	makeTimeFromDE(&mTim, td);

	uTim.actime  = mktime(&mTim);
	uTim.modtime = mktime(&mTim);
	utime(resultFile.c_str(), &uTim);
}

void fileExtract(const std::string& resultFile, MSXDirEntry* dirEntry)
{
	long size = dirEntry->size;
	int sector = clusterToSector(dirEntry->startCluster);

	FILE* file = fopen(resultFile.c_str(), "wb");
	if (!file) {
		CRITICAL_ERROR("Couldn't open file for writing!");
	}
	while (size && sector) {
		uint8_t* buf = fsImage + SECTOR_SIZE * sector;
		auto saveSize = (size > SECTOR_SIZE ? SECTOR_SIZE : size);
		fwrite(buf, 1, saveSize, file);
		size -= saveSize;
		sector = getNextSector(sector);
	}
	if (sector == 0 && size != 0) {
		std::cout << "no more sectors for file but file not ended ???\n";
	}
	fclose(file);
	// now change the access time
	changeTime(resultFile, dirEntry);
}

void recurseDirExtract(std::string_view dirName, int sector, int dirEntryIndex)
{
	int i = dirEntryIndex;
	do {
		MSXDirEntry* dirEntry = (MSXDirEntry*)((fsImage + SECTOR_SIZE * sector) + 32 * i);
		if (dirEntry->filename[0] != 0xe5 &&
		    dirEntry->filename[0] != 0x00) {
			std::string filename = condenseName(dirEntry);
			std::string fullName = !dirName.empty()
			                     ? std::string(dirName) + '/' + filename
			                     : filename;
			int td[2];
			td[0] = dirEntry->time;
			td[1] = dirEntry->date;

			tm mTim;
			makeTimeFromDE(&mTim, td);

			char tsBuf[32];
			sprintf(tsBuf, "%04d/%02d/%02d %02d:%02d:%02d",
			        mTim.tm_year + 1900, mTim.tm_mon, mTim.tm_mday,
			        mTim.tm_hour, mTim.tm_min, mTim.tm_sec);

			char osBuf[256];
			if (dirEntry->attrib & T_MSX_DIR) {
				sprintf(osBuf, "%-32s %s %12s", fullName.c_str(), tsBuf, "<dir>");
			} else {
				sprintf(osBuf, "%-32s %s %12d", fullName.c_str(), tsBuf, uint32_t(dirEntry->size));
			}
			PRT_VERBOSE(osBuf);

			if (doExtract && dirEntry->attrib != T_MSX_DIR) {
				fileExtract(fullName, dirEntry);
			}
			if (dirEntry->attrib == T_MSX_DIR) {
				mkdir_ex(fullName.c_str(), ACCESSPERMS);
				// now change the access time
				changeTime(fullName, dirEntry);
				recurseDirExtract(
				        fullName,
				        clusterToSector(dirEntry->startCluster),
				        2); // read subdir and skip entries for '.' and '..'
			}
		}
		++i;
		++dirEntry;
		if (i == NUM_OF_ENT) {
			if (sector <= rootDirEnd) {
				++sector;
				if (sector > rootDirEnd) {
					sector = 0;
				}
			} else {
				sector = getNextSector(sector);
			}
			i = 0;
			dirEntry = (MSXDirEntry*)(fsImage + SECTOR_SIZE * sector);
		}
	} while (sector != 0);
}

void readDSK(const std::string& fileName)
{
	// First read the disk image into memory

	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));

	PRT_DEBUG("trying to stat: " << fileName);
	stat(fileName.c_str(), &fst);
	size_t fsize = fst.st_size;

	dskImage = (uint8_t*)malloc(fsize);
	sizeOfDskFile = fsize;

	fsImage = dskImage;
	if (!dskImage) {
		CRITICAL_ERROR("Fatal error: Not enough memory to read image!");
	}
	// open file for reading
	PRT_DEBUG("open file for reading: " << fileName);
	FILE* file = fopen(fileName.c_str(), "rb");
	if (!file) {
		CRITICAL_ERROR("Couldn't open " << fileName << " for reading!");
	}
	if (fread(dskImage, 1, fsize, file) != fsize) {
		CRITICAL_ERROR("Error while reading from " << fileName);
	}

	// Assuming normal disk image means reading boot sector
	if (!msxPartOption) {
		if (strncmp((char*)dskImage, "T98HDDIMAGE.R0", 14) == 0 ||
		    strncmp((char*)dskImage, "\353\376\220MSX_IDE ", 11) == 0) {
			CRITICAL_ERROR("Please specify a partition to use!");
		}
		readBootSector();
	}
}

void doSpecifiedExtraction()
{
	if (optind < globalArgc) {
		PRT_VERBOSE("Going to extract only specified files/directories");
		std::string fullName = globalArgv[optind++];
		std::string_view work = fullName;
		StringOp::trimLeft(work, "/\\");

		int msxDirSector = msxChrootSector;
		int msxDirStartIndex = msxChrootStartIndex;

		// now resolv directory if needed
		auto [directory, file] = StringOp::splitOnLast(work, "/\\");
		if (!directory.empty()) {
			msxDirSector = findStartSectorOfDir(directory);
			if (msxDirSector == 0) {
				std::cout << "Couldn't find " << work << '\n';
				return;
			}
		}

		MSXDirEntry* msxDirEntry = findEntryInDir(
			makeSimpleMSXFileName(file), msxDirSector, msxDirStartIndex);
		if (!msxDirEntry) return;
		if (doExtract && msxDirEntry->attrib != T_MSX_DIR) {
			PRT_VERBOSE(fullName);
			fileExtract(fullName, msxDirEntry);
		}
		if (msxDirEntry->attrib == T_MSX_DIR) {
			recurseDirExtract(file,
			                  clusterToSector(msxDirEntry->startCluster),
			                  2); // read subdir and skip entries for '.' and '..'
		}
	} else {
		recurseDirExtract("", msxChrootSector, msxChrootStartIndex);
	}
}

void display_usage()
{
	std::cout <<
		"`msxtar' saves many files together into a single disk image to be used by\n"
		"emulators like openMSX, and can restore individual files from the archive.\n"
		"This tool supports single-sided, double-sized and IDE HD images (only FAT12)\n"
		"\n"
		"Usage: " << programName << " [OPTION]... [FILE]...\n"
		"\n"
		"Examples:\n"
		"  " << programName << " -cf disk.dsk foo bar  # Create a disk image from files/directories foo and bar.\n"
		"  " << programName << " -tvf disk.dsk         # List all files in disk.dsk verbosely.\n"
		"  " << programName << " -xf disk.dsk          # Extract all files from disk.dsk.\n"
		"\n"
		"If a long option shows an argument as mandatory, then it is mandatory\n"
		"for the equivalent short option also.  Similarly for optional arguments.\n"
		"\n"
		"Main operation mode:\n"
  		"  -t, --list              list the contents of an archive\n"
		"  -x, --extract, --get    extract files from an archive\n"
		"  -c, --create            create a new archive\n"
		"  -r, --append            append files to the end of an archive\n"
		"  -u, --update            only append files newer than copy in archive\n"
		"  -A, --catenate          append tar files to an archive\n"
		"      --concatenate       same as -A\n"
		"\n"
		"Handling of file attributes:\n"
		"      --owner=NAME             force NAME as owner for added files\n"
		"      --group=NAME             force NAME as group for added files\n"
		"      --mode=CHANGES           force (symbolic) mode CHANGES for added files\n"
		"  -k, --keep                   keep existing files, do not overwrite\n"
		"  -m, --modification-time      don't extract file modified time\n"
		"\n"
		"Image selection and switching:\n"
		"  -f, --file=ARCHIVE             use archive file or device ARCHIVE\n"
		"                                 default name is 'diskimage.dsk'\n"
		"  -S, --size=SIZE                SIZE can be nnnn[S|B|K|M]\n"
		"                                 The following simple sizes are predefined\n"
		"                                 'single' equals 360K, 'double' equals 720K\n"
		"                                 and 'ide' equals 32M\n"
		"  -1, --dos1                     use MSX-DOS1 boot sector and no subdirs\n"
  		"  -2, --dos2                     use MSX-DOS2 boot sector and use subdirs\n"
		"  -M, --msxdir=SUBDIR            place new files in SUBDIR in the image\n"
		"  -P, --partition=PART           Use partition PART when handling files\n"
		"                                 PART can be 'all' to handle all partitions"
		"\n"
		"Informative output:\n"
		"      --help            print this help, then exit\n"
		"      --version         print tar program version number, then exit\n"
		"  -v, --verbose         verbosely list files processed\n"
		"\n"
		"\n";
}

#define OPTION_STRING "12rAP:jzkmMcxf:xzwktzuS:v"

static struct option long_options[] = {
        {"dos1",              no_argument,       nullptr,       '1'},
        {"dos2",              no_argument,       nullptr,       '2'},
        {"append",            no_argument,       nullptr,       'r'},
        {"catenate",          no_argument,       nullptr,       'A'},
        {"concatenate",       no_argument,       nullptr,       'A'},
        {"bzip2",             no_argument,       nullptr,       'j'},
        {"confirmation",      no_argument,       nullptr,       'w'},
        {"create",            no_argument,       nullptr,       'c'},
        {"list",              no_argument,       nullptr,       't'},
        {"extract",           no_argument,       nullptr,       'x'},
        {"get",               no_argument,       nullptr,       'x'},
        {"file",              required_argument, nullptr,       'f'},
        {"msxdir",            required_argument, nullptr,       'M'},
        {"partition",         required_argument, nullptr,       'P'},
        {"keep",              no_argument,       nullptr,       'k'},
        {"size",              required_argument, nullptr,       'S'},
        {"gunzip",            no_argument,       nullptr,       'z'},
        {"gzip",              no_argument,       nullptr,       'z'},
        {"help",              no_argument,       &showHelp,      1 },
        {"interactive",       no_argument,       nullptr,       'w'},
        {"modification-time", no_argument,       nullptr,       'm'},
        {"keep-old-files",    no_argument,       nullptr,       'k'},
        {"ungzip",            no_argument,       nullptr,       'z'},
        {"update",            no_argument,       nullptr,       'u'},
        {"verbose",           no_argument,       nullptr,       'v'},
        {"version",           no_argument,       &showVersion,   1 },
        {"fat16",             no_argument,       &doFat16,       1 },
        {"debug",             no_argument,       nullptr, DEBUG_OPTION},
        {"bootinfo",          no_argument,       &showBootInfo,  1 },
        {nullptr, 0, nullptr, 0},
};

int main(int argc, char** argv)
{
	// code copied literally from GNU-tar.c
	// this code is to be able to handle a command like : 'tar cvf name'
	// this will be translated to 'tar -c -v -f name'

	programName = argv[0];

	// Convert old-style tar call by exploding option element and
	// rearranging options accordingly.
	if (argc > 1 && argv[1][0] != '-') {
		PRT_DEBUG("reconverting command line options");

		// Initialize a constructed option
		char buffer[3];
		buffer[0] = '-';
		buffer[2] = '\0';

		// Allocate a new argument array, and copy program name in it
		int new_argc = argc - 1 + strlen(argv[1]);
		char** new_argv = (char**)malloc((new_argc + 1) * sizeof(char*));
		char** in = argv;
		char** out = new_argv;
		*out++ = *in++;

		// Copy each old letter option as a separate option, and have
		// the corresponding argument moved next to it
		for (const char* letter = *in++; *letter; ++letter) {
			buffer[1] = *letter;
			*out++ = strdup(buffer);
			const char* cursor = strchr(OPTION_STRING, *letter);
			if (cursor && cursor[1] == ':') {
				if (in < argv + argc) {
					*out++ = *in++;
				} else {
					// this is the original line
					// USAGE_ERROR ((0, 0, _("Old option
					// `%c' requires an argument."),
					//	      *letter));
					exit(1);
				}
			}
		}

		// Copy all remaining options
		while (in < argv + argc) *out++ = *in++;
		*out = 0;

		// Replace the old option list by the new one
		argc = new_argc;
		argv = new_argv;
	}

	// Parse all options and non-options as they appear
	// quick hack need to clear this one later
	globalArgc = argc;
	globalArgv = argv;

	enum {
		CREATE_COMMAND,
		LIST_COMMAND,
		EXTRACT_COMMAND,
		UPDATE_COMMAND,
		APPEND_COMMAND
	};

	int mainCommand = LIST_COMMAND;
	int optChar;
	// default settings
	nbSectors = 1440;      // assume a DS disk is used
	sectorsPerCluster = 2; // set default value
	sizeOfDskFile = 0;

	outputFile = "diskimage.dsk";

	while (optChar = getopt_long(argc, argv, OPTION_STRING, long_options, 0),
	       optChar != -1 && optChar != 1) {
		char* optX = optarg;
		if (optX && *optX == '=') ++optX;

		switch (optChar) {
		case DEBUG_OPTION:
			showDebug = 1;
			std::cerr << "--------------------------------------------------------\n"
			             "This debug mode is intended for people who want to check\n"
			             "the dataflow within the MSXtar program.\n"
			             "Consider this mode very unpractical for normal usage :-)\n"
			             "--------------------------------------------------------\n";
			break;

		case '?':
			display_usage();

		case 0:
			break;

		case 1:
			// File name or non-parsed option, because of
			// RETURN_IN_ORDER ordering triggered by the leading
			// dash in OPTION_STRING.
			inputFile = optX;
			break;

		case '1':
			defaultBootBlock = dos1BootBlock;
			doSubdirs = false;
			break;

		case '2':
			defaultBootBlock = dos2BootBlock;
			doSubdirs = true;
			break;

		case 'c':
			mainCommand = CREATE_COMMAND;
			break;

		case 'f':
			outputFile = optX;
			break;

		case 'j':
			// set_use_compress_program_option ("bzip2");
			break;

		case 'k':
			// Don't replace existing files
			keepOption = true;
			break;

		case 'm':
			touchOption = true;
			break;

		case 'M':
			msxDirOption = true;
			msxHostDir = optX;
			break;

		case 'P':
			msxPartOption = true;
			if (strncasecmp(optX, "all", 3) == 0) {
				msxAllPart = true;
				msxPartition = 0;
			} else {
				msxPartition = strtol(optX, &optX, 10);
			}
			break;

		case 't':
			mainCommand = LIST_COMMAND;
			doExtract = false;
			++verboseOption;
			break;

		case 'u':
			mainCommand = UPDATE_COMMAND;
			break;

		case 'A':
		case 'r':
			mainCommand = APPEND_COMMAND;
			break;

		case 'v':
			++verboseOption;
			break;

		case 'x':
			mainCommand = EXTRACT_COMMAND;
			doExtract = true;
			break;
		case 'z':
			// set_use_compress_program_option ("gzip");
			break;

		case 'S':
			std::string imageSize = optX;
			if (strncasecmp(imageSize.c_str(), "single", 6) == 0) {
				nbSectors = 720;
			} else if (strncasecmp(imageSize.c_str(), "double",
			                       6) == 0) {
				nbSectors = 1440;
			} else if (strncasecmp(imageSize.c_str(), "ide", 3) ==
			           0) {
				nbSectors = 65401;
			} else {
				// first find possible 'b','k' or 'm' end character
				int size = 0;
				int scale = SECTOR_SIZE;
				char* p = optX;
				size = strtol(optX, &p, 10);
				while (*p != 0) ++p;
				--p;
				switch (*p) {
				case 'b':
				case 'B':
					scale = 1;
					break;
				case 'k':
				case 'K':
					scale = 1024;
					break;
				case 'm':
				case 'M':
					scale = 1024 * 1024;
					break;
				case 's':
				case 'S':
					scale = SECTOR_SIZE;
					break;
				}
				nbSectors = (size * scale) / SECTOR_SIZE;
			}
			break;
		}
	}

	// Process trivial options first

	if (showVersion) {
		std::cout <<
			"msxtar 0.9\n"
			"Copyright (C) 2004, the openMSX team.\n"
			"\n"
			"This program comes with NO WARRANTY, to the extent permitted by law.\n"
			"You may redistribute it under the terms of the GNU General Public License;\n"
			"see the file named COPYING for details.\n"
			"\n"
			"Written by David Heremans.\n"
			"Info provided by Jon De Schrijder and Wouter Vermaelen.\n"
			"\n";
		exit(0);
	}
	if (showHelp) {
		display_usage();
	}
	if (doFat16) {
		EOF_FAT = 0xffff;
	}

	if (argc < 2) {
		CRITICAL_ERROR("Not enough arguments");
	}

	switch (mainCommand) {
	case CREATE_COMMAND:
		createEmptyDSK();
		chroot(msxHostDir);
		PRT_DEBUG("optind " << optind << " argc " << argc);
		while (optind < argc) {
			addCreateDSK(argv[optind++]);
		}
		writeImageToDisk(outputFile);
		break;

	case LIST_COMMAND:
	case EXTRACT_COMMAND:
		readDSK(outputFile);
		if (msxPartOption) {
			if (msxAllPart) {
				for (msxPartition = 0; msxPartition < 31; ++msxPartition) {
					PRT_VERBOSE("Handling partition " << msxPartition);
					if (chPart(msxPartition)) {
						char p[40];
						sprintf(p, "./" "PARTITION%02i", msxPartition);
						std::string dirname = p;
						mkdir_ex(dirname.c_str(), ACCESSPERMS);
						recurseDirExtract(
							dirname, msxChrootSector, msxChrootStartIndex);
					}
				}
			} else {
				if (chPart(msxPartition)) {
					chroot(msxHostDir);
					doSpecifiedExtraction();
				}
			}
		} else {
			chroot(msxHostDir);
			doSpecifiedExtraction();
		}
		break;

	case APPEND_COMMAND:
		keepOption = true;
		[[fallthrough]];
	case UPDATE_COMMAND:
		readDSK(outputFile);
		if (msxPartOption) {
			if (msxAllPart) {
				CRITICAL_ERROR("Specific partition only!");
			} else {
				chPart(msxPartition);
			}
		}
		PRT_DEBUG("optind " << optind << " argc " << argc);
		chroot(msxHostDir);
		while (optind < argc) {
			updateInDSK(argv[optind++]);
		}
		writeImageToDisk(outputFile);
		break;
	}
}
