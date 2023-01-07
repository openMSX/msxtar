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
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <utime.h>

using std::cout;
using std::endl;
using std::string;

#define PRT_DEBUG(mes)                                                         \
	do {                                                                   \
		if (showDebug) {                                               \
			cout << "DEBUG: " << mes << endl;                      \
		}                                                              \
	} while (0)

#define PRT_VERBOSE(mes)                                                       \
	do {                                                                   \
		if (verboseOption) {                                           \
			cout << mes << endl;                                   \
		}                                                              \
	} while (0)

#define CRITICAL_ERROR(mes)                                                    \
	do {                                                                   \
		cout << "FATAL ERROR: " << mes << endl;                        \
		exit(1);                                                       \
	} while (0)

struct MSXBootSector {
	uint8_t jumpCode[3];           // 0xE5 to boot program
	uint8_t name[8];
	uint8_t bpSector[2];           // uint8_ts per sector (always 512)
	uint8_t spCluster[1];          // sectors per cluster (always 2)
	uint8_t resvSectors[2];        // amount of non-data sectors (ex boot sector)
	uint8_t nrFats[1];             // number of fats
	uint8_t dirEntries[2];         // max number of files in root directory
	uint8_t nrSectors[2];          // number of sectors on this disk
	uint8_t descriptor[1];         // media descriptor
	uint8_t sectorsFat[2];         // sectors per FAT
	uint8_t sectorsTrack[2];       // sectors per track
	uint8_t nrSides[2];            // number of sides
	uint8_t hiddenSectors[2];      // not used
	uint8_t bootProgram[512 - 30]; // actual boot program
};

struct MSXDirEntry {
	uint8_t filename[8];
	uint8_t ext[3];
	uint8_t attrib;
	uint8_t reserved[10]; // unused
	uint8_t time[2];
	uint8_t date[2];
	uint8_t startCluster[2];
	uint8_t size[4];
};

// Modified struct taken over from Linux' fdisk.h
struct Partition {
	uint8_t boot_ind;   // 0x80 - active
	uint8_t head;       // starting head
	uint8_t sector;     // starting sector
	uint8_t cyl;        // starting cylinder
	uint8_t sys_ind;    // What partition type
	uint8_t end_head;   // end head
	uint8_t end_sector; // end sector
	uint8_t end_cyl;    // end cylinder
	uint8_t start4[4];  // starting sector counting from 0
	uint8_t size4[4];   // nr of sectors in partition
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
string msxRootDir;
string msxHostDir;
string inputFile;
string outputFile;
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

// functions to change DirEntries
void setLE16(uint8_t* x, int y)
{
	x[0] = uint8_t((y >> 0) & 255);
	x[1] = uint8_t((y >> 8) & 255);
}
void setLE32(uint8_t* x, int y)
{
	x[0] = uint8_t((y >>  0) & 255);
	x[1] = uint8_t((y >>  8) & 255);
	x[2] = uint8_t((y >> 16) & 255);
	x[3] = uint8_t((y >> 24) & 255);
}

// functions to read DirEntries
uint16_t getLE16(const uint8_t* x)
{
	return (x[0] << 0) + (x[1] << 8);
}
int getLE32(const uint8_t* x)
{
	return (x[0] << 0) + (x[1] << 8) + (x[2] << 16) + (x[3] << 24);
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

	nbSectors = getLE16(boot->nrSectors); // assume a DS disk is used
	SECTOR_SIZE = getLE16(boot->bpSector);
	sectorsPerTrack = getLE16(boot->nrSectors);
	nbSides = getLE16(boot->nrSides);
	nbFats = (uint8_t)boot->nrFats[0];
	sectorsPerFat = getLE16(boot->sectorsFat);
	nbRootDirSectors = getLE16(boot->dirEntries) / (SECTOR_SIZE / 32);
	sectorsPerCluster = (int)(uint8_t)boot->spCluster[0];

	rootDirStart = 1 + nbFats * sectorsPerFat;
	msxChrootSector = rootDirStart;

	rootDirEnd = rootDirStart + nbRootDirSectors - 1;
	maxCluster = sectorToCluster(nbSectors);

	if (showBootInfo) {
		cout << "---------- Boot sector info -----" << endl << endl;
		cout << "  bytes per sector:      " << getLE16(boot->bpSector) << endl;
		cout << "  sectors per cluster:   " << (int)(uint8_t)boot->spCluster[0] << endl;
		cout << "  number of FAT's:       " << (int)(uint8_t)boot->nrFats[0] << endl;
		cout << "  dirEntries in rootDir: " << getLE16(boot->dirEntries) << endl;
		cout << "  sectors on disk:       " << getLE16(boot->nrSectors) << endl;
		cout << "  media descriptor:      " << std::hex << (int)boot->descriptor[0] << std::dec << endl;
		cout << "  sectors per FAT:       " << getLE16(boot->sectorsFat) << endl;
		cout << "  sectors per track:     " << getLE16(boot->sectorsTrack) << endl;
		cout << "  number of sides:       " << getLE16(boot->nrSides) << endl;
		cout << endl << "Calculated values" << endl << endl;
		cout << "maxCluster   " << maxCluster << endl;
		cout << "RootDirStart " << rootDirStart << endl;
		cout << "RootDirEnd   " << rootDirEnd << endl;
		cout << "---------------------------------" << endl << endl;
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

	setLE16(boot->nrSectors, nbSectors);
	setLE16(boot->nrSides, nbSides);
	boot->spCluster[0] = (uint8_t)nbSectorsPerCluster;
	boot->nrFats[0] = nbFats;
	setLE16(boot->sectorsFat, nbSectorsPerFat);
	setLE16(boot->dirEntries, nbDirEntry);
	boot->descriptor[0] = descriptor;
	setLE16(boot->resvSectors, nbReservedSectors);
	setLE16(boot->hiddenSectors, nbHiddenSectors);

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
		cout << "FAT size 16 not yet tested!!" << endl;
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
		cout << "FAT size 16 not yet tested!!" << endl;
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
		cout << "Disk full no more free clusters" << endl;
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
MSXDirEntry* findEntryInDir(string name, int sector, uint8_t dirEntryIndex)
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
	} while (i > NUM_OF_ENT - 1 && sector);
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
		while (newIndex > NUM_OF_ENT - 1 && sector <= rootDirEnd) {
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
			while (newIndex > NUM_OF_ENT - 1 && sector != 0) {
				int nextSector = getNextSector(sector);
				if (nextSector == 0) {
					nextSector = appendClusterToSubdir(sector);
					cout << "appendClusterToSubdir(" << sector << ") returns" << nextSector << endl;
					if (nextSector == 0) {
						CRITICAL_ERROR("disk is full");
					}
				}
				sector = nextSector;
				newIndex = findUsableIndexInSector(sector);
			}
			newEntry.sector = sector;
			newEntry.index = newIndex;
			// cout << "FATAL: subdir needs more than 16 entries" << endl;
			// exit(1);
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
string makeSimpleMSXFileName(const string& fullFilename)
{
	string::size_type pos = fullFilename.find_last_of('/');

	if (pos == string::npos)
		pos = fullFilename.find_last_of('\\'); // for DOS user :)

	string tmp;
	if (pos != string::npos) {
		tmp = fullFilename.substr(pos + 1);
	} else {
		tmp = fullFilename;
	}
	// PRT_DEBUG("filename before transform " << tmp);
	// PRT_DEBUG("filename after transform " << tmp);

	string file, ext;
	pos = tmp.find_last_of('.');
	if (pos != string::npos) {
		file = tmp.substr(0, pos);
		ext = tmp.substr(pos + 1);
	} else {
		file = tmp;
		ext = "";
	}
	// remove trailing spaces
	while (file.find_last_of(' ') == (file.size() - 1) &&
	       file.find_last_of(' ') != string::npos) {
		file = file.substr(0, file.size() - 1);
		cout << "shrinking file *" << file << "*" << endl;
	}
	while (ext.find_last_of(' ') == (ext.size() - 1) &&
	       ext.find_last_of(' ') != string::npos) {
		ext = ext.substr(0, ext.size() - 1);
		cout << "shrinking ext*" << ext << "*" << endl;
	}
	// put in major case and create '_' if needed
	transform(file.begin(), file.end(), file.begin(), toMSXChr);
	transform(ext.begin(), ext.end(), ext.begin(), toMSXChr);

	PRT_DEBUG("adding correct amount of spaces");
	file += "        ";
	ext += "   ";
	file = file.substr(0, 8);
	ext = ext.substr(0, 3);

	return file + ext;
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
	if (result.index > NUM_OF_ENT - 1) {
		cout << "couldn't add entry" << msxName << endl;
		return 0;
	}
	MSXDirEntry* dirEntry =
	        (MSXDirEntry*)(fsImage + SECTOR_SIZE * result.sector + 32 * result.index);
	dirEntry->attrib = T_MSX_DIR;
	setLE16(dirEntry->time, t);
	setLE16(dirEntry->date, d);
	memcpy(dirEntry, makeSimpleMSXFileName(msxName).c_str(), 11);

	// dirEntry->fileSize = fSize;
	uint16_t curCl = 2;
	curCl = findFirstFreeCluster();
	PRT_DEBUG("New subdir starting at cluster " << curCl);
	setLE16(dirEntry->startCluster, curCl);
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
	setLE16(dirEntry->time, t);
	setLE16(dirEntry->date, d);
	setLE16(dirEntry->startCluster, curCl);

	++dirEntry;
	memset(dirEntry, 0, sizeof(MSXDirEntry));
	memset(dirEntry, 0x20, 11); // all spaces
	memset(dirEntry, '.', 2);
	dirEntry->attrib = T_MSX_DIR;
	setLE16(dirEntry->time, t);
	setLE16(dirEntry->date, d);

	int parentCluster = sectorToCluster(sector);
	if (sector == rootDirStart) parentCluster = 0;

	setLE16(dirEntry->startCluster, parentCluster);

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
void alterFileInDSK(MSXDirEntry* msxDirEntry, string hostName)
{
	bool needsNew = false;
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(hostName.c_str(), &fst);
	int fSize = fst.st_size;

	PRT_DEBUG("AlterFileInDSK: Filesize " << fSize);

	uint16_t curCl = getLE16(msxDirEntry->startCluster);
	// if entry first used then no cluster assigned yet
	if (curCl == 0) {
		curCl = findFirstFreeCluster();
		setLE16(msxDirEntry->startCluster, curCl);
		writeFAT(curCl, EOF_FAT);
		needsNew = true;
	}
	PRT_DEBUG("AlterFileInDSK: Starting at cluster " << curCl);

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
		PRT_DEBUG("AlterFileInDSK: Continuing at cluster " << curCl);
	}
	if (file) fclose(file);

	if ((size == 0) && (curCl <= maxCluster)) {
		// TODO: check what an MSX does with filesize zero and fat allocation
		if (prevCl == 0) {
			prevCl = curCl;
			curCl = readFAT(curCl);
		}
		writeFAT(prevCl, EOF_FAT);
		PRT_DEBUG("AlterFileInDSK: Ending at cluster " << prevCl);
		// cleaning rest of FAT chain if needed
		while (!needsNew) {
			prevCl = curCl;
			if (curCl != EOF_FAT) {
				curCl = readFAT(curCl);
			} else {
				needsNew = true;
			}
			PRT_DEBUG("AlterFileInDSK: Cleaning cluster " << prevCl << " from FAT");
			writeFAT(prevCl, 0);
		}
	} else {
		// TODO: don't we need a EOF_FAT in this case as well ?
		//  find out and adjust code here
		cout << "Fake disk image full: " << hostName << " truncated.";
	}
	// write (possibly truncated) file size
	setLE32(msxDirEntry->size, fSize - size);
}

/** Add file to the MSX disk in the subdir pointed to by 'sector'
 * returns: nothing useful yet :-)
 */
void addFileToDSK(string hostName, string msxName, int sector, uint8_t dirEntryIndex)
{
	// first find out if the filename already exists current dir
	MSXDirEntry* msxDirEntry = findEntryInDir(
	        makeSimpleMSXFileName(msxName), sector, dirEntryIndex);
	if (msxDirEntry) {
		PRT_VERBOSE("Preserving entry " << msxName);
		return;
	}
	PhysDirEntry result = addEntryToDir(sector);
	if (result.index > NUM_OF_ENT - 1) {
		cout << "couldn't add entry" << hostName << endl;
		return;
	}
	MSXDirEntry* dirEntry =
	        (MSXDirEntry*)(fsImage + SECTOR_SIZE * result.sector + 32 * result.index);
	dirEntry->attrib = T_MSX_REG;

	setLE16(dirEntry->startCluster, 0);

	PRT_VERBOSE(hostName << " \t-> \"" << makeSimpleMSXFileName(msxName) << '"');
	memcpy(dirEntry, makeSimpleMSXFileName(msxName).c_str(), 11);

	// compute time/date stamps
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(hostName.c_str(), &fst);
	struct tm mtim = *localtime(&(fst.st_mtime));
	int td[2];

	makeFatTime(mtim, td);
	setLE16(dirEntry->time, td[0]);
	setLE16(dirEntry->date, td[1]);

	alterFileInDSK(dirEntry, hostName);
}

int checkStat(const string& name)
{
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));
	stat(name.c_str(), &fst);

	if (fst.st_mode & S_IFDIR) return 0; // it's a directory

	return 1; // if it's a file
}

/** transfer directory and all its subdirectories to the MSX disk image
 */
void recurseDirFill(const string& dirName, int sector, int dirEntryIndex)
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
		string name(d->d_name);
		PRT_DEBUG("reading name in dir :" << name);
		if (checkStat(dirName + '/' + name)) { // true if a file
			if (!name.empty() && name[0] != '.') {
				addFileToDSK(dirName + '/' + name, name, sector,
				             dirEntryIndex); // used here to add file into fake dsk
			} else {
				cout << name << ": ignored file which first character is \".\"" << endl;
			}
		} else if (name != "." && name != "..") {
			if (doSubdirs) {
				PRT_VERBOSE(dirName + '/' + name << " \t-> \"" << makeSimpleMSXFileName(name) << '"');
				int result;
				MSXDirEntry* msxDirEntry = findEntryInDir(
				                makeSimpleMSXFileName(name), sector, dirEntryIndex);
				if (msxDirEntry) {
					PRT_VERBOSE("Dir entry " << name << " exists already ");
					result = clusterToSector(getLE16(msxDirEntry->startCluster));
				} else {
					PRT_VERBOSE("Adding dir entry " << name);
					result = addSubDirToDSK(
					        dirName + '/' + name, name,
					        sector); // used here to add file into fake dsk
				}
				recurseDirFill(dirName + '/' + name, result, 0);
			} else {
				PRT_DEBUG("Skipping subdir:" << dirName + '/' + name);
			}
		}
		d = readdir(dir);
	}
	closedir(dir);
}

/** Save the disk image from memory to disk
 */
void writeImageToDisk(string filename)
{
	if (doTest) {
		PRT_VERBOSE("MSXtar doesn't write to disk for test");
		return; // test is not to write.
	}

	FILE* file = fopen(filename.c_str(), "wb");
	if (file) {
		if (sizeOfDskFile) {
			fwrite(dskImage, 1, sizeOfDskFile, file);
		} else {
			fwrite(dskImage, 1, nbSectors * SECTOR_SIZE, file);
		}
		fclose(file);
	} else {
		cout << "Couldn't open file for writing!";
	}
}

void updateCreateDSK(const string fileName)
{
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));

	PRT_DEBUG("trying to stat : " << fileName);
	stat(fileName.c_str(), &fst);
	if (fst.st_mode & S_IFDIR) {
		// this should be a directory
		if (doFlat || !doSubdirs) {
			// put files in the directory to root
			recurseDirFill(fileName, msxChrootSector, msxChrootStartIndex);
		} else {
			PRT_VERBOSE("./" + fileName << " \t-> \"" << makeSimpleMSXFileName(fileName) << '"');
			int result;
			MSXDirEntry* msxDirEntry = findEntryInDir(
			        makeSimpleMSXFileName(fileName),
			        msxChrootSector, msxChrootStartIndex);
			if (msxDirEntry) {
				PRT_VERBOSE("Dir entry " << fileName << " exists already ");
				result = clusterToSector(getLE16(msxDirEntry->startCluster));
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
		// addFileToDSK(fileName,fileName,MSXchrootSector,MSXchrootStartIndex); // used here to add file into fake dsk in root dir!!
		// first find out if the filename already exists current dir
		MSXDirEntry* msxDirEntry =
		        findEntryInDir(makeSimpleMSXFileName(fileName),
		                       msxChrootSector, msxChrootStartIndex);
		alterFileInDSK(msxDirEntry, fileName);
	}
}

void addCreateDSK(const string fileName)
{
	// Here we create the fake disk images based upon the files that can be
	// found in the 'fileName' directory or the single file
	// PRT_DEBUG("Trying FDC_DirAsDSK image");
	PRT_DEBUG("addCreateDSK(" << fileName << ");");
	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));

	PRT_DEBUG("addCreateDSK: trying to stat : " << fileName);
	stat(fileName.c_str(), &fst);
	if (fst.st_mode & S_IFDIR) {
		// this should be a directory
		PRT_VERBOSE("addCreateDSK: adding directory " << fileName);

		if (doFlat || !doSubdirs) {
			// put files in the directory to root
			msxRootDir = fileName;
			recurseDirFill(fileName, msxChrootSector, msxChrootStartIndex);
		} else {
			PRT_VERBOSE("./" + fileName << " \t-> \"" << makeSimpleMSXFileName(fileName) << '"');
			int result;
			MSXDirEntry* msxDirEntry = findEntryInDir(
			        makeSimpleMSXFileName(fileName),
			        msxChrootSector, msxChrootStartIndex);
			if (msxDirEntry) {
				PRT_VERBOSE("Dir entry " << fileName << " exists already ");
				result = clusterToSector(getLE16(msxDirEntry->startCluster));
			} else {
				PRT_VERBOSE("Adding dir entry " << fileName);
				result = addSubDirToDSK(fileName, fileName, msxChrootSector);
				// used here to add file into fake dsk
			}
			recurseDirFill(fileName, result, 0);
		}
	} else {
		// this should be a normal file
		PRT_DEBUG("addCreateDSK: Adding file " << fileName);
		PRT_VERBOSE("Adding file " << fileName);
		addFileToDSK(fileName, fileName, msxChrootSector,
		             msxChrootStartIndex); // used here to add file into fake dsk in root dir!!
	}
}

void updateInDSK(string name)
{
	// delete last character in the filename if it's a character to divide.

	if (name.length() > 0) {
		unsigned char ch = *(name.end() - 1);
		if (ch == '/' && ch == '\\') { // TODO BUG
			name.erase(name.length() - 1);
		}
		// Erased last character because it's a kind of slash :)
	}

	// first find the filename in the current 'root dir'
	MSXDirEntry* msxDirEntry = findEntryInDir(makeSimpleMSXFileName(name), rootDirStart, 0);
	if (!msxDirEntry) {
		PRT_VERBOSE("Couldn't find entry "
		            << name
		            << " to update, trying to create new entry");
		addCreateDSK(name);
	} else {
		if (keepOption) {
			PRT_VERBOSE("Preserving entry " << name);
		} else {
			// PRT_VERBOSE("Updating entry not yet implemented " << name);
			updateCreateDSK(name);
		}
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
		PRT_DEBUG("Not enough memory for disk image");
		// throw MSXException("No sufficient memory available");
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
		fsImage[SECTOR_SIZE + 0] = boot->descriptor[0];
	}
	fsImage[SECTOR_SIZE + 1] = 0xFF;
	fsImage[SECTOR_SIZE + 2] = 0xFF;
}

string condenseName(MSXDirEntry* dirEntry)
{
	char condensedName[13];
	int i;
	char* p = condensedName;
	for (i = 0; i < 8; ++i) {
		if (dirEntry->filename[i] == ' ') {
			i = 9;
		} else {
			*(p++) = tolower(dirEntry->filename[i]);
		}
	}
	if (dirEntry->ext[0] != ' ' || dirEntry->ext[1] != ' ' ||
	    dirEntry->ext[2] != ' ') {
		*(p++) = '.';
		for (i = 0; i < 3; ++i) {
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
		cout << "T98header recognized" << endl;
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
		cout << "Not an idefdisk compatible 0 sector" << endl;
		return false;
	}
	Partition* p = (Partition*)(dskImage + 14 + (30 - chPartition) * 16);
	if (getLE32(p->start4) == 0) {
		return false;
	}
	fsImage = dskImage + SECTOR_SIZE * getLE32(p->start4);
	readBootSector();
	return true;
}

/** Routine to get the first sector of a given dir name
 * input: correctly MSXformatted subdirectory name
 * returns: 0 if given directory not found
 */
int findStartSectorOfDir(string dirname)
{
	string work = dirname;
	string totalPath = ".";
	int msxDirSector = msxChrootSector;
	int msxDirStartIndex = msxChrootStartIndex;
	// if (!msxDirOption){return;}
	while (!work.empty()) {
		// cout << "chroot 0: work=" << work << endl;
		// remove (multiple)leading '/'
		while (work.find_first_of("/\\") == 0) {
			work.erase(0, 1);
			// cout << "chroot 1: work=" << work << endl;
		}
		string firstPart;
		string::size_type pos = work.find_first_of("/\\");
		if (pos != string::npos) {
			firstPart = work.substr(0, pos);
			work = work.substr(pos + 1);
		} else {
			firstPart = work;
			work.clear();
		}
		// find firstPart directory
		string simple = makeSimpleMSXFileName(firstPart);
		MSXDirEntry* msxDirEntry =
		        findEntryInDir(simple, msxDirSector, msxDirStartIndex);
		if (!msxDirEntry) {
			PRT_VERBOSE("Couldn't find directory: " << dirname);
			return 0;
		}
		msxDirSector = clusterToSector(getLE16(msxDirEntry->startCluster));
		msxDirStartIndex = 2;
		totalPath += '/' + firstPart;
		mkdir_ex(totalPath.c_str(), ACCESSPERMS);
	}
	return msxDirSector;
}

// routine to update the global vars: MSXchrootSector, MSXchrootStartIndex
void chroot()
{
	string work = msxHostDir;

	// if (!msxDirOption){return;}
	while (!work.empty()) {
		cout << "chroot 0: work=" << work << endl;
		// remove (multiple)leading '/'
		while (work.find_first_of('/') == 0) {
			work.erase(0, 1);
			cout << "chroot 1: work=" << work << endl;
		}
		string firstPart;
		string::size_type pos = work.find_first_of('/');
		if (pos != string::npos) {
			firstPart = work.substr(0, pos);
			work = work.substr(pos + 1);
		} else {
			firstPart = work;
			work.clear();
		}
		// find firstPart directory or create it
		string simple = makeSimpleMSXFileName(firstPart);
		MSXDirEntry* msxDirEntry = findEntryInDir(
		        simple, msxChrootSector, msxChrootStartIndex);
		if (!msxDirEntry) {
			// creat new subdir
			time_t now;
			time(&now);
			struct tm mtim = *localtime(&now);
			int td[2];
			makeFatTime(mtim, td);

			cout << "Create subdir " << endl;
			msxChrootSector = addMSXSubdir(simple, td[0], td[1], msxChrootSector);
			msxChrootStartIndex = 2;
			if (msxChrootSector == 0) {
				exit(0);
			}
		} else {
			msxChrootSector = clusterToSector(getLE16(msxDirEntry->startCluster));
			msxChrootStartIndex = 2;
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
void changeTime(string resultFile, MSXDirEntry* dirEntry)
{
	if (touchOption) return;

	int td[2];
	td[0] = getLE16(dirEntry->time);
	td[1] = getLE16(dirEntry->date);

	struct tm mTim;
	struct utimbuf uTim;
	makeTimeFromDE(&mTim, td);

	uTim.actime  = mktime(&mTim);
	uTim.modtime = mktime(&mTim);
	utime(resultFile.c_str(), &uTim);
}

void fileExtract(string resultFile, MSXDirEntry* dirEntry)
{
	long size = getLE32(dirEntry->size);
	int sector = clusterToSector(getLE16(dirEntry->startCluster));

	FILE* file = fopen(resultFile.c_str(), "wb");
	if (!file) {
		CRITICAL_ERROR("Couldn't open file for writing!");
	}
	while (size && sector) {
		uint8_t* buf = fsImage + SECTOR_SIZE * sector;
		long saveSize = (size > SECTOR_SIZE ? SECTOR_SIZE : size);
		fwrite(buf, 1, saveSize, file);
		size -= saveSize;
		sector = getNextSector(sector);
	}
	if (sector == 0 && size != 0) {
		cout << "no more sectors for file but file not ended ???"
		     << endl;
	}
	fclose(file);
	// now change the access time
	changeTime(resultFile, dirEntry);
}

void recurseDirExtract(const string& dirName, int sector, int dirEntryIndex)
{
	int i = dirEntryIndex;
	do {
		MSXDirEntry* dirEntry = (MSXDirEntry*)((fsImage + SECTOR_SIZE * sector) + 32 * i);
		if (dirEntry->filename[0] != 0xe5 &&
		    dirEntry->filename[0] != 0x00) {
			string filename = condenseName(dirEntry);
			string fullName = filename;
			if (!dirName.empty()) {
				fullName = dirName + '/' + filename;
			}
			int td[2];
			td[0] = getLE16(dirEntry->time);
			td[1] = getLE16(dirEntry->date);

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
				sprintf(osBuf, "%-32s %s %12d", fullName.c_str(), tsBuf, getLE32(dirEntry->size));
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
				        clusterToSector(getLE16(dirEntry->startCluster)),
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

void readDSK(const string fileName)
{
	// First read the disk image into memory

	struct stat fst;
	memset(&fst, 0, sizeof(struct stat));

	PRT_DEBUG("trying to stat : " << fileName);
	stat(fileName.c_str(), &fst);
	size_t fsize = fst.st_size;

	dskImage = (uint8_t*)malloc(fsize);
	sizeOfDskFile = fsize;

	fsImage = dskImage;
	if (!dskImage) {
		CRITICAL_ERROR("Fatal error: Not enough memory to read image!");
	}
	// open file for reading
	PRT_DEBUG("open file for reading : " << fileName);
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
			cout << "Please specify a partition to use!" << endl;
			exit(1);
		}
		readBootSector();
	}
}

void doSpecifiedExtraction()
{
	if (optind < globalArgc) {
		PRT_VERBOSE("Going to extract only specified files/directories");
		string work = globalArgv[optind++];
		string fullName = work;
		// remove (multiple)leading '/'
		while (work.find_first_of("/\\") == 0) {
			work.erase(0, 1);
		}
		int msxDirSector = msxChrootSector;
		int msxDirStartIndex = msxChrootStartIndex;
		// now resolv directory if needed
		string::size_type pos = work.find_last_of("/\\");
		if (pos != string::npos) {
			string firstPart = work.substr(0, pos);
			work = work.substr(pos + 1);
			msxDirSector = findStartSectorOfDir(firstPart);
			if (msxDirSector == 0) {
				cout << "Couldn't find " << work << endl;
				return;
			}
		}

		MSXDirEntry* msxDirEntry = findEntryInDir(
			makeSimpleMSXFileName(work), msxDirSector, msxDirStartIndex);
		if (!msxDirEntry) return;
		if (doExtract && msxDirEntry->attrib != T_MSX_DIR) {
			PRT_VERBOSE(fullName);
			fileExtract(fullName, msxDirEntry);
		}
		if (msxDirEntry->attrib == T_MSX_DIR) {
			recurseDirExtract(work,
			                  clusterToSector(getLE16(msxDirEntry->startCluster)),
			                  2); // read subdir and skip entries for '.' and '..'
		}
	} else {
		recurseDirExtract("", msxChrootSector, msxChrootStartIndex);
	}
}

void display_usage()
{
	printf("\
`msxtar' saves many files together into a single disk image to be used by\n\
emulators like openMSX, and can restore individual files from the archive.\n\
This tool supports single-sided, double-sized and IDE HD images (only FAT12)\n");
	printf("\nUsage: %s [OPTION]... [FILE]...\n\
\n\
Examples:\n\
  %s -cf disk.dsk foo bar  # Create a disk image from files/directories foo and bar.\n\
  %s -tvf disk.dsk         # List all files in disk.dsk verbosely.\n\
  %s -xf disk.dsk          # Extract all files from disk.dsk.\n",
	       programName, programName, programName, programName);
	printf("\
\n\
If a long option shows an argument as mandatory, then it is mandatory\n\
for the equivalent short option also.  Similarly for optional arguments.\n");
	printf("\
\n\
Main operation mode:\n\
  -t, --list              list the contents of an archive\n\
  -x, --extract, --get    extract files from an archive\n\
  -c, --create            create a new archive\n\
  -r, --append            append files to the end of an archive\n\
  -u, --update            only append files newer than copy in archive\n\
  -A, --catenate          append tar files to an archive\n\
      --concatenate       same as -A\n");

	printf("\
\n\
Handling of file attributes:\n\
      --owner=NAME             force NAME as owner for added files\n\
      --group=NAME             force NAME as group for added files\n\
      --mode=CHANGES           force (symbolic) mode CHANGES for added files\n\
  -k, --keep                   keep existing files, do not overwrite \n\
  -m, --modification-time      don't extract file modified time\n");
	printf("\
\n\
Image selection and switching:\n\
  -f, --file=ARCHIVE             use archive file or device ARCHIVE\n\
                                 default name is 'diskimage.dsk'\n\
  -S, --size=SIZE                SIZE can be nnnn[S|B|K|M]\n\
                                 The following simple sizes are predefined\n\
                                 'single' equals 360K, 'double' equals 720K\n\
                                 and 'ide' equals 32M\n\
  -1, --dos1                     use MSX-DOS1 boot sector and no subdirs\n\
  -2, --dos2                     use MSX-DOS2 boot sector and use subdirs\n\
  -M, --msxdir=SUBDIR            place new files in SUBDIR in the image\n\
  -P, --partition=PART           Use partition PART when handling files\n\
                                 PART can be 'all' to handle all partitions");

	printf("\
\n\
Informative output:\n\
      --help            print this help, then exit\n\
      --version         print tar program version number, then exit\n\
  -v, --verbose         verbosely list files processed\n");
	printf("\n\n");
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

	outputFile = string("diskimage.dsk");

	while (optChar = getopt_long(argc, argv, OPTION_STRING, long_options, 0),
	       optChar != -1 && optChar != 1) {
		char* optX = optarg;
		if (optX && *optX == '=') ++optX;

		switch (optChar) {
		case DEBUG_OPTION:
			showDebug = 1;
			cout << "----------------------------------------------------------" << endl;
			cout << "This debug mode is intended for people who want to check  " << endl;
			cout << "the dataflow within the MSXtar program.                   " << endl;
			cout << "Consider this mode very unpractical for normal usage :-)  " << endl;
			cout << "----------------------------------------------------------" << endl;
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
			string imageSize = optX;
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
				cout << "Final letter" << *p << endl;
				cout << "value is " << size << endl;
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
		printf("msxtar 0.9\n");
		printf("Copyright (C) 2004, the openMSX team.\n\n");
		printf("\
This program comes with NO WARRANTY, to the extent permitted by law.\n\
You may redistribute it under the terms of the GNU General Public License;\n\
see the file named COPYING for details.\n");
		printf("Written by David Heremans.\n");
		printf("Info provided by Jon De Schrijder and Wouter Vermaelen.\n\n");
		exit(0);
	}
	if (showHelp) {
		display_usage();
	}
	if (doFat16) {
		EOF_FAT = 0xffff;
	}

	if (argc < 2) {
		cout << "Not enough arguments" << endl;
	} else {
		PRT_DEBUG("Testing switch command");
		switch (mainCommand) {
		case CREATE_COMMAND:
			createEmptyDSK();
			chroot();
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
							string dirname = p;
							mkdir_ex(dirname.c_str(), ACCESSPERMS);
							recurseDirExtract(
							        dirname, msxChrootSector, msxChrootStartIndex);
						}
					}
				} else {
					if (chPart(msxPartition)) {
						chroot();
						doSpecifiedExtraction();
					}
				}
			} else {
				chroot();
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
					cout << "Specific partition only!" << endl;
					exit(1);
				} else {
					chPart(msxPartition);
				}
			}
			PRT_DEBUG("optind " << optind << " argc " << argc);
			chroot();
			while (optind < argc) {
				updateInDSK(argv[optind++]);
			}
			writeImageToDisk(outputFile);
			break;
		}
	}
}
