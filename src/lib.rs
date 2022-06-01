// SPDX-FileCopyrightText: 2022 Brian Kubisiak <brian@kubisiak.com>
//
// SPDX-License-Identifier: MIT

use std::convert::TryInto;
use std::ffi::OsStr;
use std::fs::File;
use std::io::{Error, ErrorKind, Read, Result, Seek, SeekFrom};
use std::ops::{Add, Div, Sub};
use std::os::unix::ffi::OsStrExt;
use std::path::{Component, Path, PathBuf};

fn read_le16<R: Read>(f: &mut R) -> Result<u16> {
    let mut buf = [0; 2];
    f.read_exact(&mut buf)?;
    return Ok(u16::from_le_bytes(buf));
}

fn read_le32<R: Read>(f: &mut R) -> Result<u32> {
    let mut buf = [0; 4];
    f.read_exact(&mut buf)?;
    return Ok(u32::from_le_bytes(buf));
}

fn read_le64<R: Read>(f: &mut R) -> Result<u64> {
    let mut buf = [0; 8];
    f.read_exact(&mut buf)?;
    return Ok(u64::from_le_bytes(buf));
}

fn ceil_div<T: Add<Output = T> + Div<Output = T> + Sub<Output = T> + Copy>(
    num: T,
    den: T,
    one: T,
) -> T {
    return (num + den - one) / den;
}

fn get<T>(table: &[T], idx: usize) -> Result<&T> {
    match table.get(idx) {
        Some(v) => return Ok(v),
        None => {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "index out of range",
            ))
        }
    }
}

const MAGIC: u32 = 0x73717368;
const MAJOR: u16 = 4;
const MINOR: u16 = 0;

const META_LEN: usize = 8192;

struct Metadata {
    length: usize,
    data: [u8; 8192],
}

impl Metadata {
    fn from<R: Read>(f: &mut R) -> Result<Metadata> {
        let hdr = read_le16(f)?;
        let compressed = (hdr & (1 << 15)) == 0;
        let length = (hdr & !(1 << 15)) as usize;
        if length > META_LEN {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "metadata block too long",
            ));
        }

        if compressed {
            return Err(Error::new(
                ErrorKind::Unsupported,
                "compressed metadata not supported",
            ));
        }
        let mut data = [0; META_LEN];
        f.read_exact(&mut data[0..length])?;

        return Ok(Metadata { length, data });
    }
}

struct MetadataReader<'a, R: Read + Seek> {
    mb: Metadata,
    f: &'a mut R,
    offset: usize,
}

impl<'a, R: Read + Seek> MetadataReader<'a, R> {
    fn open(f: &mut R, loc: u64, offset: usize) -> Result<MetadataReader<R>> {
        f.seek(SeekFrom::Start(loc))?;
        let mb = Metadata::from(f)?;

        return Ok(MetadataReader { f, mb, offset });
    }

    pub fn remaining_in_block(&self) -> usize {
        return self.mb.length - self.offset;
    }
}

impl<'a, R: Read + Seek> Read for MetadataReader<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        while self.offset >= META_LEN {
            self.mb = Metadata::from(&mut self.f)?;
            self.offset -= META_LEN;
        }

        let bytes_to_read = std::cmp::min(buf.len(), META_LEN - self.offset);

        let end_idx = self.offset + bytes_to_read;
        buf[0..bytes_to_read]
            .copy_from_slice(&self.mb.data[self.offset..end_idx]);
        self.offset += bytes_to_read;

        return Ok(bytes_to_read);
    }
}

enum Compression {
    Zlib,
    Lzma,
    Lzo,
    Xz,
    Lz4,
    Zstd,
    Unknown(u16),
}

impl Compression {
    fn from(i: u16) -> Compression {
        match i {
            1 => Compression::Zlib,
            2 => Compression::Lzma,
            3 => Compression::Lzo,
            4 => Compression::Xz,
            5 => Compression::Lz4,
            6 => Compression::Zstd,
            _ => Compression::Unknown(i),
        }
    }
}

struct Flags {
    f: u16,
}

impl Flags {
    const NOI: u16 = 1 << 0;
    const NOD: u16 = 1 << 1;
    const NOF: u16 = 1 << 3;
    const NO_FRAG: u16 = 1 << 4;
    const ALWAYS_FRAG: u16 = 1 << 5;
    const DUPLICATE: u16 = 1 << 6;
    const EXPORT: u16 = 1 << 7;
    const COMP_OPT: u16 = 1 << 10;
    const NOID: u16 = 1 << 11;

    fn from(f: u16) -> Flags {
        return Flags { f };
    }

    fn check(&self, v: u16) -> bool {
        return (self.f & v) != 0;
    }

    fn noi(&self) -> bool {
        return self.check(Flags::NOI);
    }

    fn nod(&self) -> bool {
        return self.check(Flags::NOD);
    }

    fn nof(&self) -> bool {
        return self.check(Flags::NOF);
    }

    fn no_frag(&self) -> bool {
        return self.check(Flags::NO_FRAG);
    }

    fn always_frag(&self) -> bool {
        return self.check(Flags::ALWAYS_FRAG);
    }

    fn duplicate(&self) -> bool {
        return self.check(Flags::DUPLICATE);
    }

    fn export(&self) -> bool {
        return self.check(Flags::EXPORT);
    }

    fn comp_opt(&self) -> bool {
        return self.check(Flags::COMP_OPT);
    }

    fn noid(&self) -> bool {
        return self.check(Flags::NOID);
    }
}

struct SuperBlock {
    inodes: u32,
    block_size: u32,
    fragments: u32,
    compression: Compression,
    flags: Flags,
    no_ids: usize,
    root_inode: u64,
    bytes_used: u64,
    id_table_start: u64,
    _xattr_id_table_start: u64,
    inode_table_start: u64,
    directory_table_start: u64,
    fragment_table_start: u64,
    lookup_table_start: u64,
}

impl SuperBlock {
    fn from<R: Read>(f: &mut R) -> Result<SuperBlock> {
        let magic = read_le32(f)?;
        if magic != MAGIC {
            return Err(Error::new(ErrorKind::InvalidData, "bad magic number"));
        }

        let inodes = read_le32(f)?;
        let _mkfs_time = read_le32(f)?;
        let block_size = read_le32(f)?;
        let fragments = read_le32(f)?;

        let compression = Compression::from(read_le16(f)?);
        if let Compression::Unknown(_) = compression {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "invalid compression",
            ));
        }

        let block_log = read_le16(f)?;
        if 1 << block_log != block_size {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "corrupted superblock",
            ));
        }

        let flags = Flags::from(read_le16(f)?);
        let no_ids = read_le16(f)? as usize;

        let major = read_le16(f)?;
        let minor = read_le16(f)?;
        if major != MAJOR || minor != MINOR {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "unrecognized version",
            ));
        }

        let root_inode = read_le64(f)?;
        let bytes_used = read_le64(f)?;
        let id_table_start = read_le64(f)?;
        let xattr_id_table_start = read_le64(f)?;
        let inode_table_start = read_le64(f)?;
        let directory_table_start = read_le64(f)?;
        let fragment_table_start = read_le64(f)?;
        let lookup_table_start = read_le64(f)?;

        return Ok(SuperBlock {
            inodes,
            block_size,
            fragments,
            compression,
            flags,
            no_ids,
            root_inode,
            bytes_used,
            id_table_start,
            _xattr_id_table_start: xattr_id_table_start,
            inode_table_start,
            directory_table_start,
            fragment_table_start,
            lookup_table_start,
        });
    }
}

enum InodeType {
    Dir(DirInode),
    Reg(RegInode),
    Symlink(SymlinkInode),
    Blkdev(DevInode),
    Chrdev(DevInode),
    Fifo(IpcInode),
    Socket(IpcInode),
    LDir(LDirInode),
    LReg(LRegInode),
    LSymlink(LSymlinkInode),
    LBlkdev(LDevInode),
    LChrdev(LDevInode),
    LFifo(LIpcInode),
    LSocket(LIpcInode),
}

impl InodeType {
    fn from<R: Read>(n: u16, f: &mut R, block_size: u32) -> Result<InodeType> {
        return match n {
            1 => Ok(InodeType::Dir(DirInode::from(f)?)),
            2 => Ok(InodeType::Reg(RegInode::from(f, block_size)?)),
            3 => Ok(InodeType::Symlink(SymlinkInode::from(f)?)),
            4 => Ok(InodeType::Blkdev(DevInode::from(f)?)),
            5 => Ok(InodeType::Chrdev(DevInode::from(f)?)),
            6 => Ok(InodeType::Fifo(IpcInode::from(f)?)),
            7 => Ok(InodeType::Socket(IpcInode::from(f)?)),
            8 => Ok(InodeType::LDir(LDirInode::from(f)?)),
            9 => Ok(InodeType::LReg(LRegInode::from(f, block_size)?)),
            10 => Ok(InodeType::LSymlink(LSymlinkInode::from(f)?)),
            11 => Ok(InodeType::LBlkdev(LDevInode::from(f)?)),
            12 => Ok(InodeType::LChrdev(LDevInode::from(f)?)),
            13 => Ok(InodeType::LFifo(LIpcInode::from(f)?)),
            14 => Ok(InodeType::LSocket(LIpcInode::from(f)?)),
            x => Err(Error::new(
                ErrorKind::InvalidData,
                format!("unrecognized inode type: {}", x),
            )),
        };
    }

    fn to(&self) -> Type {
        return match self {
            InodeType::Dir(_) => Type::Directory,
            InodeType::LDir(_) => Type::Directory,
            InodeType::Reg(_) => Type::Regular,
            InodeType::LReg(_) => Type::Regular,
            InodeType::Symlink(_) => Type::Symlink,
            InodeType::LSymlink(_) => Type::Symlink,
            InodeType::Blkdev(_) => Type::BlockDevice,
            InodeType::LBlkdev(_) => Type::BlockDevice,
            InodeType::Chrdev(_) => Type::CharDevice,
            InodeType::LChrdev(_) => Type::CharDevice,
            InodeType::Fifo(_) => Type::Fifo,
            InodeType::LFifo(_) => Type::Fifo,
            InodeType::Socket(_) => Type::Fifo,
            InodeType::LSocket(_) => Type::Fifo,
        };
    }
}

struct Inode {
    inode_type: InodeType,
    mode: u16,
    uid: u32,
    guid: u32,
    mtime: u32,
    inode_number: u32,
}

impl Inode {
    fn from<R: Read>(
        f: &mut R,
        id_table: &[u32],
        block_size: u32,
    ) -> Result<Inode> {
        let inode_type = read_le16(f)?;
        let mode = read_le16(f)?;
        let uid = *get(id_table, read_le16(f)? as usize)?;
        let guid = *get(id_table, read_le16(f)? as usize)?;
        let mtime = read_le32(f)?;
        let inode_number = read_le32(f)?;

        let inode_type = InodeType::from(inode_type, f, block_size)?;

        return Ok(Inode {
            inode_type,
            mode,
            uid,
            guid,
            mtime,
            inode_number,
        });
    }

    fn to(self, name: PathBuf) -> Squashinfo {
        let typ = self.inode_type.to();

        return Squashinfo {
            name,
            typ,
            inode: self,
        };
    }

    fn is_dir(&self) -> bool {
        return match self.inode_type {
            InodeType::Dir(_) => true,
            InodeType::LDir(_) => true,
            _ => false,
        };
    }
}

struct IpcInode {
    _nlink: u32,
}

impl IpcInode {
    fn from<R: Read>(f: &mut R) -> Result<IpcInode> {
        let nlink = read_le32(f)?;
        return Ok(IpcInode { _nlink: nlink });
    }
}

struct LIpcInode {
    _nlink: u32,
    _xattr: u32,
}

impl LIpcInode {
    fn from<R: Read>(f: &mut R) -> Result<LIpcInode> {
        let nlink = read_le32(f)?;
        let xattr = read_le32(f)?;

        return Ok(LIpcInode {
            _nlink: nlink,
            _xattr: xattr,
        });
    }
}

struct DevInode {
    _nlink: u32,
    rdev: u32,
}

impl DevInode {
    fn from<R: Read>(f: &mut R) -> Result<DevInode> {
        let nlink = read_le32(f)?;
        let rdev = read_le32(f)?;

        return Ok(DevInode {
            _nlink: nlink,
            rdev,
        });
    }
}

struct LDevInode {
    _nlink: u32,
    rdev: u32,
    _xattr: u32,
}

impl LDevInode {
    fn from<R: Read>(f: &mut R) -> Result<LDevInode> {
        let nlink = read_le32(f)?;
        let rdev = read_le32(f)?;
        let xattr = read_le32(f)?;

        return Ok(LDevInode {
            _nlink: nlink,
            rdev,
            _xattr: xattr,
        });
    }
}

struct SymlinkInode {
    _nlink: u32,
    symlink: Vec<u8>,
}

impl SymlinkInode {
    fn from<R: Read>(f: &mut R) -> Result<SymlinkInode> {
        let nlink = read_le32(f)?;
        let symlink_size = read_le32(f)? as usize;

        let mut symlink = vec![0; symlink_size];
        f.read_exact(&mut symlink)?;

        return Ok(SymlinkInode {
            _nlink: nlink,
            symlink,
        });
    }
}

// note that lsym inodes are not supported in linux
struct LSymlinkInode {
    _nlink: u32,
    symlink: Vec<u8>,
    _xattr: u32,
}

impl LSymlinkInode {
    fn from<R: Read>(f: &mut R) -> Result<LSymlinkInode> {
        let nlink = read_le32(f)?;
        let symlink_size = read_le32(f)? as usize;

        let mut symlink = vec![0; symlink_size];
        f.read_exact(&mut symlink)?;

        let xattr = read_le32(f)?;

        return Ok(LSymlinkInode {
            _nlink: nlink,
            symlink,
            _xattr: xattr,
        });
    }
}

struct RegInode {
    start_block: u32,
    fragment: u32,
    offset: u32,
    file_size: u32,
    block_list: Vec<u32>,
}

impl RegInode {
    fn from<R: Read>(f: &mut R, block_size: u32) -> Result<RegInode> {
        let start_block = read_le32(f)?;
        let fragment = read_le32(f)?;
        let offset = read_le32(f)?;
        let file_size = read_le32(f)?;

        let block_count = if fragment == 0xFFFFFFFF {
            ceil_div(file_size, block_size, 1)
        } else {
            file_size / block_size
        };

        let mut block_list = Vec::new();
        for _ in 0..block_count {
            block_list.push(read_le32(f)?);
        }

        return Ok(RegInode {
            start_block,
            fragment,
            offset,
            file_size,
            block_list,
        });
    }
}

struct LRegInode {
    start_block: u64,
    file_size: u64,
    sparse: u64,
    _nlink: u32,
    fragment: u32,
    offset: u32,
    _xattr: u32,
    block_list: Vec<u32>,
}

impl LRegInode {
    fn from<R: Read>(f: &mut R, block_size: u32) -> Result<LRegInode> {
        let start_block = read_le64(f)?;
        let file_size = read_le64(f)?;
        let sparse = read_le64(f)?;
        let nlink = read_le32(f)?;
        let fragment = read_le32(f)?;
        let offset = read_le32(f)?;
        let xattr = read_le32(f)?;

        let block_count = if fragment == 0xFFFFFFFF {
            ceil_div(file_size, block_size as u64, 1)
        } else {
            file_size / (block_size as u64)
        };

        let mut block_list = Vec::new();
        for _ in 0..block_count {
            block_list.push(read_le32(f)?);
        }

        return Ok(LRegInode {
            start_block,
            file_size,
            sparse,
            _nlink: nlink,
            fragment,
            offset,
            _xattr: xattr,
            block_list,
        });
    }
}

struct DirInode {
    start_block: u32,
    _nlink: u32,
    file_size: u16,
    offset: u16,
    parent_inode: u32,
}

impl DirInode {
    fn from<R: Read>(f: &mut R) -> Result<DirInode> {
        let start_block = read_le32(f)?;
        let nlink = read_le32(f)?;
        let file_size = read_le16(f)?;
        let offset = read_le16(f)?;
        let parent_inode = read_le32(f)?;

        return Ok(DirInode {
            start_block,
            _nlink: nlink,
            file_size,
            offset,
            parent_inode,
        });
    }

    fn list<'a, R: Read + Seek>(
        &self,
        sf: &'a mut Squashfile<R>,
    ) -> Result<DirListing<'a, R>> {
        // the on-disk value is 3 bytes larger than the actual listing, which
        // the linux kernel uses for implicitly generating "." and ".."
        let remaining_size = (self.file_size - 3) as u32;

        // we don't actually read the header here; instead, that happens lazily
        // during actual iteration
        let remaining_entries = 0;
        let inode_reference = 0;
        let inode_md_offset = 0;

        let md_loc = (self.start_block as u64) + sf.sb.directory_table_start;
        sf.f.seek(SeekFrom::Start(md_loc))?;
        let md = Metadata::from(&mut sf.f)?;

        let md_offset = self.offset as usize;
        let next_md_position = sf.f.stream_position()?;

        Ok(DirListing {
            sf,
            remaining_size,
            remaining_entries,
            inode_reference,
            inode_md_offset,
            md,
            md_offset,
            next_md_position,
        })
    }
}

struct DirIndex {
    index: u32,
    start_block: u32,
    name: Vec<u8>,
}

impl DirIndex {
    fn from<R: Read>(f: &mut R) -> Result<DirIndex> {
        let index = read_le32(f)?;
        let start_block = read_le32(f)?;
        let size = (read_le32(f)? as u64) + 1;

        let mut name = Vec::<u8>::with_capacity(size as usize);
        name.resize(size as usize, 0);
        f.read_exact(&mut name[..])?;

        return Ok(DirIndex {
            index,
            start_block,
            name,
        });
    }
}

struct LDirInode {
    _nlink: u32,
    file_size: u32,
    start_block: u32,
    parent_inode: u32,
    offset: u16,
    _xattr: u32,
    index: Vec<DirIndex>,
}

impl LDirInode {
    fn from<R: Read>(f: &mut R) -> Result<LDirInode> {
        let nlink = read_le32(f)?;
        let file_size = read_le32(f)?;
        let start_block = read_le32(f)?;
        let parent_inode = read_le32(f)?;
        let num_indices = read_le16(f)?;
        let offset = read_le16(f)?;
        let xattr = read_le32(f)?;

        let mut index = Vec::new();
        for _ in 0..num_indices {
            index.push(DirIndex::from(f)?);
        }

        return Ok(LDirInode {
            _nlink: nlink,
            file_size,
            start_block,
            parent_inode,
            offset,
            _xattr: xattr,
            index,
        });
    }

    fn list<'a, R: Read + Seek>(
        &self,
        sf: &'a mut Squashfile<R>,
    ) -> Result<DirListing<'a, R>> {
        // the on-disk value is 3 bytes larger than the actual listing, which
        // the linux kernel uses for implicitly generating "." and ".."
        let remaining_size = self.file_size - 3;

        // we don't actually read the header here; instead, that happens lazily
        // during actual iteration
        let remaining_entries = 0;
        let inode_reference = 0;
        let inode_md_offset = 0;

        let md_loc = (self.start_block as u64) + sf.sb.directory_table_start;
        sf.f.seek(SeekFrom::Start(md_loc))?;
        let md = Metadata::from(&mut sf.f)?;

        let md_offset = self.offset as usize;
        let next_md_position = sf.f.stream_position()?;

        Ok(DirListing {
            sf,
            remaining_size,
            remaining_entries,
            inode_reference,
            inode_md_offset,
            md,
            md_offset,
            next_md_position,
        })
    }
}

/// Top-level class for interfacing with a squashfs archive.
pub struct Squashfile<R: Read + Seek> {
    sb: SuperBlock,
    id_table: Vec<u32>,
    fragment_table: Vec<FragmentEntry>,
    f: R,
}

/// Enum indicating the high-level type of an inode inside the squashfs archive.
#[derive(Debug, PartialEq)]
pub enum Type {
    Regular,
    Symlink,
    Directory,
    Fifo,
    CharDevice,
    BlockDevice,
}

impl Squashfile<File> {
    /// Open a squashfs archive from a file for reading
    ///
    /// # Arguments
    ///
    /// * `filename` - The path to the squashfs archive file to open
    pub fn open(filename: &str) -> Result<Squashfile<File>> {
        let f = File::open(filename)?;
        return Squashfile::from(f);
    }
}

impl<R: Read + Seek> Squashfile<R> {
    /// Parse a squashfs archive for reading from an existing reader.
    ///
    /// # Arguments
    ///
    /// * `f` - Readable/seekable input device from which to read the archive data
    pub fn from(mut f: R) -> Result<Squashfile<R>> {
        let sb = SuperBlock::from(&mut f)?;
        let id_table = Squashfile::load_id_table(&mut f, &sb)?;
        let fragment_table = Squashfile::load_fragment_table(&mut f, &sb)?;
        return Ok(Squashfile {
            sb,
            id_table,
            fragment_table,
            f,
        });
    }

    fn load_id_table(f: &mut R, sb: &SuperBlock) -> Result<Vec<u32>> {
        // compute the number of metadata blocks based on the number of 32-bit
        // id entries in the id table
        let block_count =
            ceil_div(sb.no_ids * std::mem::size_of::<u32>(), META_LEN, 1);

        // the location list maps entries to metadata block offsets
        let mut loc_list = Vec::new();
        f.seek(SeekFrom::Start(sb.id_table_start))?;
        for _ in 0..block_count {
            loc_list.push(read_le64(f)?);
        }

        let mut id_table = Vec::new();
        for md_loc in loc_list {
            f.seek(SeekFrom::Start(md_loc))?;
            let md = Metadata::from(f)?;

            for i in 0..(md.length / std::mem::size_of::<u32>()) {
                let id_bytes: [u8; 4] = [
                    md.data[i + 0],
                    md.data[i + 1],
                    md.data[i + 2],
                    md.data[i + 3],
                ];
                let id = u32::from_le_bytes(id_bytes);
                id_table.push(id);
            }
        }

        debug_assert_eq!(id_table.len(), sb.no_ids);
        return Ok(id_table);
    }

    fn load_fragment_table(
        f: &mut R,
        sb: &SuperBlock,
    ) -> Result<Vec<FragmentEntry>> {
        let fragment_entry_size =
            std::mem::size_of::<u64>() + 2 * std::mem::size_of::<u32>();
        let block_count = ceil_div(
            (sb.fragments as usize) * fragment_entry_size,
            META_LEN,
            1,
        );

        let mut loc_list = Vec::new();
        f.seek(SeekFrom::Start(sb.fragment_table_start))?;
        for _ in 0..block_count {
            loc_list.push(read_le64(f)?);
        }

        let mut fragment_table = Vec::new();
        let mut remaining_fragments = sb.fragments;
        for md_loc in loc_list {
            let mut md = MetadataReader::open(f, md_loc, 0)?;

            while md.remaining_in_block() > 0 && remaining_fragments > 0 {
                debug_assert_eq!(
                    md.remaining_in_block() % fragment_entry_size,
                    0
                );
                let archive_offset = read_le64(&mut md)?;
                let on_disk_size = read_le32(&mut md)?;
                let _unused = read_le32(&mut md)?;
                let compressed = (on_disk_size >> 24) == 0;
                let on_disk_size = on_disk_size & 0x00ffffff;

                fragment_table.push(FragmentEntry {
                    archive_offset,
                    on_disk_size,
                    compressed,
                });

                remaining_fragments -= 1;
            }
        }

        debug_assert_eq!(fragment_table.len(), sb.fragments as usize);
        return Ok(fragment_table);
    }

    pub fn has_compressed_inodes(&self) -> bool {
        return !self.sb.flags.noi();
    }

    pub fn has_compressed_data(&self) -> bool {
        return !self.sb.flags.nod();
    }

    pub fn has_compressed_fragments(&self) -> bool {
        return !self.sb.flags.nof();
    }

    pub fn has_fragments(&self) -> bool {
        return !self.sb.flags.no_frag();
    }

    pub fn always_fragment(&self) -> bool {
        return self.sb.flags.always_frag();
    }

    pub fn data_is_deduplicated(&self) -> bool {
        return self.sb.flags.duplicate();
    }

    pub fn has_export_table(&self) -> bool {
        return self.sb.flags.export();
    }

    pub fn has_compressor_options(&self) -> bool {
        return self.sb.flags.comp_opt();
    }

    pub fn has_compressed_id_table(&self) -> bool {
        // note that uncompressed inodes implies uncompressed id tables in
        // squashfs-tools; linux does not use this flag
        return !self.sb.flags.noid() && !self.sb.flags.noi();
    }

    /// Get a list of all UIDs/GIDs present in the archive.
    pub fn ids(&self) -> &[u32] {
        return &self.id_table;
    }

    fn find_inode_offset(
        &mut self,
        md_offset: u64,
        inode_offset: usize,
    ) -> Result<Inode> {
        let block_size = self.sb.block_size;
        let md_loc = self.sb.inode_table_start + md_offset;
        let mut md_reader =
            MetadataReader::open(&mut self.f, md_loc, inode_offset)?;

        return Inode::from(&mut md_reader, &self.id_table, block_size);
    }

    fn find_inode(&mut self, inode: u64) -> Result<Inode> {
        // lower 16 bits are the offset within the uncompressed md block, upper
        // bits are the offset of the md block itself
        let md_offset = (inode >> 16) as u64;
        let inode_offset = (inode & ((1 << 16) - 1)) as usize;
        self.find_inode_offset(md_offset, inode_offset)
    }

    fn root(&mut self) -> Result<Inode> {
        return Ok(self.find_inode(self.sb.root_inode)?);
    }

    /// Look up metadata corresponding to the given path inside the archive
    ///
    /// # Arguments
    ///
    /// * `name` - Absolute path to look up within the archive
    ///
    /// # Examples
    ///
    /// ```
    /// use squashfile::Squashfile;
    /// use std::path::Path;
    /// let mut squashfile = Squashfile::open("tests/foo.squashfs").unwrap();
    /// let squashinfo = squashfile.getmember(Path::new("./foo.txt"));
    /// ```
    pub fn getmember(&mut self, name: &Path) -> Result<Squashinfo> {
        let components = name.components();

        let mut res = self.root()?;
        for component in components {
            if component == Component::CurDir {
                continue;
            }

            // TODO: this will fail if there is a ".." component, since these
            // are implicit rather than explicit
            let mut found = false;
            let listing = match &res.inode_type {
                InodeType::Dir(d) => d.list(self),
                InodeType::LDir(d) => d.list(self),
                _ => {
                    return Err(Error::new(
                        ErrorKind::InvalidData, // TODO: NotADirectory
                        component.as_os_str().to_string_lossy(),
                    ));
                }
            };
            for (name, dentry) in listing? {
                if Component::Normal(name.as_os_str()) == component {
                    res = dentry;
                    found = true;
                    break;
                }
            }
            if !found {
                return Err(Error::new(
                    ErrorKind::NotFound,
                    component.as_os_str().to_string_lossy(),
                ));
            }
        }

        return Ok(res.to(name.to_path_buf()));
    }

    pub fn extractfile<'a>(
        &'a mut self,
        file: &'a Squashinfo,
    ) -> Result<FileReader<'a, R>> {
        match &file.inode.inode_type {
            InodeType::Reg(f) => {
                let fragment = if f.fragment == 0xffffffff {
                    None
                } else {
                    Some((f.fragment, f.offset))
                };
                self.f.seek(SeekFrom::Start(f.start_block as u64))?;
                return Ok(FileReader {
                    sq: self,
                    block_list: &f.block_list,
                    block_idx: 0,
                    remaining_in_file: f.file_size as u64,
                    remaining_in_block: 0,
                    fragment,
                    block: vec![],
                });
            }
            InodeType::LReg(f) => {
                let fragment = if f.fragment == 0xffffffff {
                    None
                } else {
                    Some((f.fragment, f.offset))
                };
                self.f.seek(SeekFrom::Start(f.start_block))?;
                return Ok(FileReader {
                    sq: self,
                    block_list: &f.block_list,
                    block_idx: 0,
                    remaining_in_file: f.file_size,
                    remaining_in_block: 0,
                    fragment,
                    block: vec![],
                });
            }
            _ => {
                return Err(Error::new(ErrorKind::InvalidData, "not a file"));
            }
        }
    }

    /// Iterate over the entire directory tree in a squashfile
    pub fn walk(&mut self) -> Result<SquashIter<R>> {
        let root_inode = self.root()?;
        let root_name = PathBuf::from(".");
        let stack = vec![(root_name, root_inode)];

        return Ok(SquashIter { sq: self, stack });
    }
}

struct FragmentEntry {
    archive_offset: u64,
    on_disk_size: u32,
    compressed: bool,
}

pub struct SquashIter<'a, R: Read + Seek> {
    sq: &'a mut Squashfile<R>,
    stack: Vec<(PathBuf, Inode)>,
}

impl<'a, R: Read + Seek> SquashIter<'a, R> {
    fn add_dir_listing(
        stack: &mut Vec<(PathBuf, Inode)>,
        name: &Path,
        listing: DirListing<R>,
    ) {
        for (entry_name, dentry) in listing {
            let full_path: PathBuf =
                [name, entry_name.as_path()].iter().collect();
            stack.push((full_path, dentry));
        }
    }

    fn get_next_entry(
        &mut self,
        name: &Path,
        inode: Inode,
    ) -> Result<Squashinfo> {
        match &inode.inode_type {
            InodeType::Dir(d) => SquashIter::add_dir_listing(
                &mut self.stack,
                &name,
                d.list(self.sq)?,
            ),
            InodeType::LDir(d) => SquashIter::add_dir_listing(
                &mut self.stack,
                &name,
                d.list(self.sq)?,
            ),
            _ => {}
        }
        return Ok(inode.to(name.to_path_buf()));
    }
}

impl<'a, R: Read + Seek> Iterator for SquashIter<'a, R> {
    type Item = Result<Squashinfo>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.stack.pop() {
            None => {
                // reset the iterator so the caller can re-use this archive
                return None;
            }
            Some((name, inode)) => {
                return Some(self.get_next_entry(name.as_path(), inode));
            }
        }
    }
}

struct DirListing<'a, R: Read + Seek> {
    sf: &'a mut Squashfile<R>,
    remaining_size: u32,
    remaining_entries: u32,
    inode_reference: i32,
    inode_md_offset: u64,
    md: Metadata,
    md_offset: usize,
    next_md_position: u64,
}

struct DirEntry {
    offset: u16,
    _inode_offset: i16,
    _typ: u16,
    name: PathBuf,
}

impl<'a, R: Read + Seek> DirListing<'a, R> {
    fn load_next_metadata(&mut self) -> Result<()> {
        self.sf.f.seek(SeekFrom::Start(self.next_md_position))?;
        let md = Metadata::from(&mut self.sf.f)?;
        self.md = md;
        self.md_offset = 0;
        self.next_md_position = self.sf.f.stream_position()?;
        Ok(())
    }

    fn load_byte(&mut self) -> Result<u8> {
        if self.md_offset == META_LEN {
            self.load_next_metadata()?;
        }

        self.md_offset += 1;
        return Ok(self.md.data[self.md_offset - 1]);
    }

    fn load_next_header(&mut self) {
        // there are no more additional headers
        if self.remaining_size == 0 {
            return;
        }

        // I'm not sure how this could happen unless the squashfile is malformed
        // or my directory listing code is incorrect
        if self.remaining_size < 12 {
            panic!(
                "not enough space for directory header ({})!",
                self.remaining_size
            );
        }

        let hdr_buf: Result<Vec<u8>> =
            (0..12).map(|_| self.load_byte()).collect();
        self.remaining_size -= 12;
        // TODO: proper error handling here
        let hdr_buf = hdr_buf.unwrap();
        // the number of entries is stored off-by-one (ie 0 indicates 1 entry);
        // empty directories have the size set to 0 in the inode instead
        let count = u32::from_le_bytes(hdr_buf[0..4].try_into().unwrap()) + 1;
        let start = u32::from_le_bytes(hdr_buf[4..8].try_into().unwrap());
        let inode_number =
            i32::from_le_bytes(hdr_buf[8..12].try_into().unwrap());

        self.remaining_entries = count;
        self.inode_reference = inode_number;
        self.inode_md_offset = start as u64;
    }

    fn load_next_entry(&mut self) -> Option<DirEntry> {
        if self.remaining_entries == 0 {
            self.load_next_header();
        }
        // if loading the next header produces no additional entries, we are at
        // the end of the listing
        if self.remaining_entries == 0 {
            return None;
        }

        if self.remaining_size < 8 {
            panic!(
                "not enough space for directory entry ({})!",
                self.remaining_size
            );
        }

        let entry_buf: Result<Vec<u8>> =
            (0..8).map(|_| self.load_byte()).collect();
        self.remaining_size -= 8;
        self.remaining_entries -= 1;
        let entry_buf = entry_buf.unwrap();

        let offset = u16::from_le_bytes(entry_buf[0..2].try_into().unwrap());
        let inode_offset =
            i16::from_le_bytes(entry_buf[2..4].try_into().unwrap());
        let typ = u16::from_le_bytes(entry_buf[4..6].try_into().unwrap());
        // since a zero-length name makes no sense, it is stored off-by-one
        let name_size =
            (u16::from_le_bytes(entry_buf[6..8].try_into().unwrap()) + 1)
                as u32;

        if self.remaining_size < name_size {
            panic!(
                "not enough space for entry name ({}, {})!",
                self.remaining_size, name_size
            );
        }

        let name_buf: Result<Vec<u8>> =
            (0..name_size).map(|_| self.load_byte()).collect();
        self.remaining_size -= name_size;
        let name_buf = name_buf.unwrap();
        let os_name = OsStr::from_bytes(&name_buf);
        let name = Path::new(os_name).to_path_buf();

        return Some(DirEntry {
            offset,
            _inode_offset: inode_offset,
            _typ: typ,
            name,
        });
    }
}

impl<'a, R: Read + Seek> Iterator for DirListing<'a, R> {
    type Item = (PathBuf, Inode);

    fn next(&mut self) -> Option<Self::Item> {
        let entry = self.load_next_entry()?;
        let inode = self
            .sf
            .find_inode_offset(self.inode_md_offset, entry.offset as usize)
            .unwrap();
        return Some((entry.name, inode));
    }
}

pub struct FileReader<'a, R: Read + Seek> {
    sq: &'a mut Squashfile<R>,
    block_list: &'a [u32],
    block_idx: usize,
    remaining_in_block: usize,
    remaining_in_file: u64,
    block: Vec<u8>,
    fragment: Option<(u32, u32)>,
}

impl<'a, R: Read + Seek> FileReader<'a, R> {
    fn maybe_load_fragment(&mut self) -> Result<()> {
        debug_assert!(self.remaining_in_file < self.sq.sb.block_size as u64);
        if let Some((fragment_idx, fragment_offset)) = self.fragment {
            let fragment = get(&self.sq.fragment_table, fragment_idx as usize)?;
            assert!(!fragment.compressed);
            // note that this assertion only works when compression is disabled
            debug_assert!(
                self.remaining_in_file + (fragment_offset as u64)
                    <= fragment.on_disk_size as u64
            );

            self.block.resize(self.remaining_in_file as usize, 0);
            self.sq.f.seek(SeekFrom::Start(
                fragment.archive_offset + (fragment_offset as u64),
            ))?;
            self.sq.f.read_exact(&mut self.block[..])?;

            self.remaining_in_block = self.remaining_in_file as usize;
            self.remaining_in_file = 0;
            return Ok(());
        } else {
            return Ok(());
        }
    }

    fn load_next_block(&mut self) -> Result<()> {
        // we've reached eof; load a fragment now if one exists
        if self.block_idx == self.block_list.len() {
            return self.maybe_load_fragment();
        }

        let is_compressed = (self.block_list[self.block_idx] >> 24) == 0
            && self.block_list[self.block_idx] != 0;
        if is_compressed {
            panic!("compressed data blocks are not yet supported!");
        }

        let mut on_disk_size =
            (self.block_list[self.block_idx] & 0x00ffffff) as u64;

        // sparse data block; we can zero out the buffer without reading data
        if on_disk_size == 0 {
            on_disk_size = std::cmp::min(
                self.remaining_in_file,
                self.sq.sb.block_size as u64,
            );
            // TODO: there's probably a better way to do this
            self.block.clear();
            self.block.resize(on_disk_size as usize, 0);
        } else {
            on_disk_size =
                std::cmp::min(self.remaining_in_file, on_disk_size as u64);
            // expand the block buffer if needed
            self.block.resize(on_disk_size as usize, 0);
            self.sq.f.read_exact(&mut self.block[..])?;
        }

        self.remaining_in_file -= on_disk_size as u64;
        self.remaining_in_block = on_disk_size as usize;
        self.block_idx += 1;

        return Ok(());
    }
}

impl<'a, R: Read + Seek> Read for FileReader<'a, R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        if self.remaining_in_block == 0 && self.remaining_in_file == 0 {
            return Ok(0);
        }

        if self.remaining_in_block == 0 {
            self.load_next_block()?;
        }

        let bytes_to_read = std::cmp::min(self.remaining_in_block, buf.len());

        let start_idx = self.block.len() - self.remaining_in_block;
        let end_idx = start_idx + bytes_to_read;
        buf[0..bytes_to_read].copy_from_slice(&self.block[start_idx..end_idx]);

        self.remaining_in_block -= bytes_to_read;

        debug_assert!(bytes_to_read != 0 || self.remaining_in_file == 0);
        return Ok(bytes_to_read);
    }
}

/// Metadata for a single entry inside a squashfs archive.
pub struct Squashinfo {
    /// Path to this entry inside the archive.
    pub name: PathBuf,
    /// Type of this entry.
    pub typ: Type,

    inode: Inode,
}

impl Squashinfo {
    pub fn mode(&self) -> u16 {
        return self.inode.mode;
    }

    pub fn mtime(&self) -> u32 {
        return self.inode.mtime;
    }

    pub fn uid(&self) -> u32 {
        return self.inode.uid;
    }

    pub fn gid(&self) -> u32 {
        return self.inode.guid;
    }

    pub fn linkname(&self) -> Option<&[u8]> {
        return match &self.inode.inode_type {
            InodeType::Symlink(s) => Some(&s.symlink),
            InodeType::LSymlink(s) => Some(&s.symlink),
            _ => None,
        };
    }

    /// Get the size of a file in a squash archive
    ///
    /// This will return the size (in bytes) of a regular file inside
    /// the archive. For non-regular files (eg symlinks, directories,
    /// etc), this will return None.
    pub fn size(&self) -> Option<u64> {
        match &self.inode.inode_type {
            InodeType::Reg(f) => Some(f.file_size as u64),
            InodeType::LReg(f) => Some(f.file_size),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Squashfile, Squashinfo, Type};
    use std::{io::Read, path::Path};

    #[test]
    fn check_id_table() {
        let sq = Squashfile::open("tests/foo.squashfs").unwrap();
        let ids = sq.ids();
        assert_eq!(ids, [0]);
    }

    #[test]
    fn check_root() {
        let mut sq = Squashfile::open("tests/foo.squashfs").unwrap();
        let root = sq.getmember(Path::new("./")).unwrap();
        assert_eq!(root.typ, Type::Directory);
        assert_eq!(root.mtime(), 1);
        assert_eq!(root.mode(), 0o777);
        assert_eq!(root.uid(), 0);
        assert_eq!(root.gid(), 0);
    }

    #[test]
    fn find_file() {
        let mut sq = Squashfile::open("tests/foo.squashfs").unwrap();
        let foo = sq.getmember(Path::new("./foo.txt")).unwrap();
        assert_eq!(foo.typ, Type::Regular);
        assert_eq!(foo.mtime(), 1);
        assert_eq!(foo.mode(), 0o644);
        assert_eq!(foo.uid(), 0);
        assert_eq!(foo.gid(), 0);
    }

    #[test]
    fn list_files() {
        let mut sq = Squashfile::open("tests/foo.squashfs").unwrap();
        let members: Vec<Squashinfo> =
            sq.walk().unwrap().map(|f| f.unwrap()).collect();
        assert_eq!(members.len(), 2);
        assert_eq!(members[0].name, Path::new("."));
        assert_eq!(members[1].name, Path::new("./foo.txt"));
    }

    #[test]
    fn read_foo() {
        let mut sq = Squashfile::open("tests/foo.squashfs").unwrap();
        let foo_info = sq.getmember(Path::new("./foo.txt")).unwrap();
        let mut foo = sq.extractfile(&foo_info).unwrap();
        let mut buf = [0; 4];
        let cnt = foo.read(&mut buf).unwrap();
        assert_eq!(cnt, 4);
        assert_eq!(buf, [b'f', b'o', b'o', b'\n']);
        let cnt = foo.read(&mut buf).unwrap();
        assert_eq!(cnt, 0);
    }

    #[test]
    fn check_count() {
        let mut sq = Squashfile::open("tests/count.squashfs").unwrap();
        let members: Vec<Squashinfo> =
            sq.walk().unwrap().map(|f| f.unwrap()).collect();
        assert_eq!(members.len(), 7);
    }

    #[test]
    fn check_count_contents() {
        let mut sq = Squashfile::open("tests/count.squashfs").unwrap();
        let mut buf = [0; 10];
        let f = sq.getmember(Path::new("./1.txt")).unwrap();
        let mut v = sq.extractfile(&f).unwrap();
        let cnt = v.read(&mut buf).unwrap();
        assert_eq!(cnt, 2);
        assert_eq!(buf[0..2], vec![b'1', b'\n']);
        let f = sq.getmember(Path::new("./2/3.txt")).unwrap();
        let mut v = sq.extractfile(&f).unwrap();
        let cnt = v.read(&mut buf).unwrap();
        assert_eq!(cnt, 0);
        let f = sq.getmember(Path::new("./4/5/6.txt")).unwrap();
        let mut v = sq.extractfile(&f).unwrap();
        let cnt = v.read(&mut buf).unwrap();
        assert_eq!(cnt, 2);
        assert_eq!(buf[0..2], vec![b'6', b'\n']);
    }

    #[test]
    fn check_sparse_file() {
        let mut sq = Squashfile::open("tests/sparse.squashfs").unwrap();
        let f = sq.getmember(Path::new("./zero.bin")).unwrap();
        let mut v = sq.extractfile(&f).unwrap();
        let mut buf = [0; 16];
        let cnt = v.read(&mut buf).unwrap();
        assert_eq!(cnt, 16);
        assert_eq!(buf, [0; 16]);
        let cnt = v.read(&mut buf).unwrap();
        assert_eq!(cnt, 0);
    }

    #[test]
    fn check_fragment() {
        let mut sq = Squashfile::open("tests/fragment.squashfs").unwrap();
        let f = sq.getmember(Path::new("./fragment.txt")).unwrap();
        let mut v = sq.extractfile(&f).unwrap();
        let mut buf = [0; 19];
        let cnt = v.read(&mut buf).unwrap();
        assert_eq!(cnt, 19);
        assert_eq!(
            buf,
            [
                b't', b'h', b'i', b's', b' ', b'i', b's', b' ', b'a', b' ',
                b'f', b'r', b'a', b'g', b'm', b'e', b'n', b't', b'\n'
            ]
        );
        let cnt = v.read(&mut buf).unwrap();
        assert_eq!(cnt, 0);
    }

    #[test]
    fn check_symlink() {
        let mut sq = Squashfile::open("tests/symlink.squashfs").unwrap();
        let foo = sq.getmember(Path::new("./foo.txt")).unwrap();
        assert_eq!(foo.linkname(), None);
        let bar = sq.getmember(Path::new("./bar.txt")).unwrap();
        assert_eq!(bar.linkname().unwrap(), b"foo.txt");
    }

    #[test]
    fn check_flags() {
        let sq = Squashfile::open("tests/fragment.squashfs").unwrap();
        assert!(!sq.has_compressed_inodes());
        assert!(!sq.has_compressed_data());
        assert!(!sq.has_compressed_id_table());
        assert!(!sq.has_compressed_fragments());
        assert!(!sq.always_fragment());
        assert!(sq.data_is_deduplicated());
        assert!(!sq.has_compressor_options());
        assert!(sq.has_fragments());
        assert!(sq.has_export_table());
    }
}
