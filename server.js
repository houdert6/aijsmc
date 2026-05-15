const WebSocket = require('ws');
const wss = new WebSocket.Server({host: '0.0.0.0', port: 25565 });

// --- SERVER WORLD STATE ---
// players: id -> {id, x, y, z, dim, username, mode, health, maxHealth, inventory: { type: count }, lastDamageTime: 0}
const players = new Map(); 
const mobs = [];
// worldBlocks: "x,y,z,dim" -> { type: string, state: object }
const worldBlocks = new Map(); 
const villagePOIs = []; // Store interesting locations {x, y, z, type}
let hostId = null;

// Timing & Day/Night Cycle
let prevTime = performance.now();
let worldTime = 0;
const DAY_DURATION = 600; // Seconds for a full day/night cycle

// Config
const WORLD_SIZE = 40;
const BLOCK_SIZE = 5;

// Helper
const getKey = (x, y, z, dim) => `${Math.round(x)},${Math.round(y)},${Math.round(z)},${dim}`;

// Unbreakable blocks in Survival
const UNBREAKABLE_BLOCKS = ['bedrock', 'end_frame', 'end_frame_filled', 'portal', 'network_block'];

// --- WORLD GENERATION ---
function simpleNoise(x, z) { return Math.abs(Math.sin(x*0.1) + Math.cos(z*0.1)) * 2; }

function generateOverworld() {
    for (let x = -WORLD_SIZE/2; x < WORLD_SIZE/2; x++) {
        for (let z = -WORLD_SIZE/2; z < WORLD_SIZE/2; z++) {
            const xp = x * BLOCK_SIZE;
            const zp = z * BLOCK_SIZE;
            const yHeight = Math.floor(simpleNoise(x, z));
            addBlock(xp, yHeight * BLOCK_SIZE, zp, 'grass', 'overworld');
            for(let d=1; d<=2; d++) addBlock(xp, (yHeight - d) * BLOCK_SIZE, zp, 'dirt', 'overworld');
            
            if (x > -10 && x < 10 && z > -10 && z < 10) { 
                if (Math.random() > 0.96) createTree(xp, (yHeight + 1) * BLOCK_SIZE, zp, 'overworld');
            }

            if (Math.random() < 0.02) {
                const type = Math.random() > 0.6 ? 'zombie' : 'villager';
                spawnMob(type, xp, (yHeight + 2) * BLOCK_SIZE, zp, 'overworld');
            }
        }
    }
    generateDesert();
}

function generateDesert() {
    const offset = 30; 
    const size = 60;
    for (let x = 0; x < size; x++) {
        for (let z = -size/2; z < size/2; z++) {
            const worldX = (x + offset) * BLOCK_SIZE;
            const worldZ = z * BLOCK_SIZE;
            const h = Math.sin(x * 0.1) * 1.5 + Math.cos(z * 0.1) * 1.5;
            const yHeight = Math.floor(h);
            addBlock(worldX, yHeight * BLOCK_SIZE, worldZ, 'sand', 'overworld');
            addBlock(worldX, (yHeight - 1) * BLOCK_SIZE, worldZ, 'sand', 'overworld');
            addBlock(worldX, (yHeight - 2) * BLOCK_SIZE, worldZ, 'stone', 'overworld');
            if (Math.random() > 0.99) {
                const ch = Math.floor(Math.random() * 2) + 2; 
                for(let cy=1; cy<=ch; cy++) addBlock(worldX, (yHeight + cy) * BLOCK_SIZE, worldZ, 'cactus', 'overworld');
            }
        }
    }
    generateVillage((offset + size/2) * BLOCK_SIZE, 0 * BLOCK_SIZE);
}

// --- RANDOMIZED VILLAGE GENERATION ---
function generateVillage(cx, cz) {
    const dim = 'overworld';
    const villageY = 2 * BLOCK_SIZE; 
    
    // Main Street Spine
    const streetLength = 50;
    for(let z = -streetLength; z <= streetLength; z+=BLOCK_SIZE) {
        for(let x = -5; x <= 5; x+=BLOCK_SIZE) {
             addBlock(cx + x, villageY, cz + z, 'stone', dim);
        }
    }
    
    // Iterate along the street to place structures
    const step = 20; // Distance between plots
    for(let z = -streetLength + 10; z <= streetLength - 10; z += step) {
        // Left Side (-x)
        if (Math.random() > 0.3) { // 70% chance to have something
            const type = Math.random() > 0.7 ? 'farm' : 'house'; // 30% Farm, 70% House
            const px = cx - 15 * BLOCK_SIZE;
            const pz = cz + z * BLOCK_SIZE;
            
            if (type === 'house') {
                buildHouse(px, villageY + BLOCK_SIZE, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'house' });
            } else {
                buildFarm(px - 10*BLOCK_SIZE, villageY, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'farm' });
            }
        }

        // Right Side (+x)
        if (Math.random() > 0.3) {
            const type = Math.random() > 0.7 ? 'farm' : 'house';
            const px = cx + 15 * BLOCK_SIZE;
            const pz = cz + z * BLOCK_SIZE;
            
            if (type === 'house') {
                buildHouse(px, villageY + BLOCK_SIZE, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'house' });
            } else {
                buildFarm(px + 10*BLOCK_SIZE, villageY, pz, dim);
                villagePOIs.push({ x: px, y: villageY + BLOCK_SIZE, z: pz, type: 'farm' });
            }
        }
    }
    
    // Random Villagers
    const count = 5 + Math.floor(Math.random() * 8);
    for(let i=0; i<count; i++) {
        const vx = cx + (Math.random() - 0.5) * 40 * BLOCK_SIZE;
        const vz = cz + (Math.random() - 0.5) * 100 * BLOCK_SIZE;
        spawnMob('villager', vx, villageY + 5 * BLOCK_SIZE, vz, dim);
    }
}

function buildHouse(x, y, z, dim) {
    for(let i=0; i<5; i++) {
        for(let k=0; k<5; k++) {
            const bx = x + (i-2)*BLOCK_SIZE;
            const bz = z + (k-2)*BLOCK_SIZE;
            
            // Foundation Logic
            for(let fy = y - BLOCK_SIZE; fy > -50; fy -= BLOCK_SIZE) {
                const kKey = getKey(bx, fy, bz, dim);
                if (worldBlocks.has(kKey)) break;
                addBlock(bx, fy, bz, 'stone', dim);
            }

            for(let j=0; j<4; j++) {
                const by = y + j*BLOCK_SIZE;
                if (i===0 || i===4 || k===0 || k===4 || j===0) {
                    if (j===0) addBlock(bx, by, bz, 'stone', dim);
                    else {
                        // Door Logic: Front wall (k==0), center (i==2), height 0 & 1
                        if (i===2 && k===0 && j < 2) {
                            // Default door state: closed
                            addBlock(bx, by, bz, 'door', dim, { open: false });
                            continue;
                        }
                        
                        if (j < 3 && i===2 && k===0) continue;
                        if (j===2 && (i===0 || i===4 || k===4)) { continue; }
                        addBlock(bx, by, bz, 'sand', dim);
                    }
                }
            }
            const topY = y + 4*BLOCK_SIZE;
            addBlock(bx, topY, bz, 'wood', dim);
        }
    }
}

function buildFarm(x, y, z, dim) {
    for(let i=0; i<7; i++) {
        for(let k=0; k<7; k++) {
            const bx = x + (i-3)*BLOCK_SIZE;
            const bz = z + (k-3)*BLOCK_SIZE;
            
            // Foundation Logic
            for(let fy = y - BLOCK_SIZE; fy > -50; fy -= BLOCK_SIZE) {
                const kKey = getKey(bx, fy, bz, dim);
                if (worldBlocks.has(kKey)) break;
                addBlock(bx, fy, bz, 'stone', dim);
            }

            if (i===0 || i===6 || k===0 || k===6) {
                addBlock(bx, y+BLOCK_SIZE, bz, 'wood', dim);
            } else {
                if (i===3) {
                    addBlock(bx, y, bz, 'water', dim);
                } else {
                    addBlock(bx, y, bz, 'dirt', dim);
                    addBlock(bx, y+BLOCK_SIZE, bz, 'crop', dim);
                }
            }
        }
    }
}

function generateEndWorld() {
    const size = 15;
    for (let x = -size; x < size; x++) {
        for (let z = -size; z < size; z++) {
            const dist = Math.sqrt(x*x + z*z);
            if (dist < size - Math.random() * 3) {
                const xp = x * BLOCK_SIZE;
                const zp = z * BLOCK_SIZE;
                addBlock(xp, 0, zp, 'end_stone', 'the_end');
                addBlock(xp, -BLOCK_SIZE, zp, 'end_stone', 'the_end');
            }
        }
    }
    const pillars = [[8, 8], [-8, -8], [8, -8], [-8, 8]];
    pillars.forEach(coord => {
        const h = 5 + Math.floor(Math.random() * 5);
        for(let y=1; y<h; y++) addBlock(coord[0] * BLOCK_SIZE, y * BLOCK_SIZE, coord[1] * BLOCK_SIZE, 'obsidian', 'the_end');
        spawnMob('end_crystal', coord[0] * BLOCK_SIZE, (h) * BLOCK_SIZE + 1.5, coord[1] * BLOCK_SIZE, 'the_end');
    });
    addBlock(0, BLOCK_SIZE, -5 * BLOCK_SIZE, 'network_block', 'the_end');
}

function createTree(x, y, z, dim) {
    for(let i=0; i<4; i++) addBlock(x, y + (i*BLOCK_SIZE), z, 'wood', dim);
    const topY = y + (4*BLOCK_SIZE);
    for(let lx=-1; lx<=1; lx++) {
        for(let lz=-1; lz<=1; lz++) {
            for(let ly=0; ly<=1; ly++) {
                    if(lx===0 && lz===0 && ly===0) continue;
                    addBlock(x + (lx*BLOCK_SIZE), topY + (ly*BLOCK_SIZE), z + (lz*BLOCK_SIZE), 'leaves', dim);
            }
        }
    }
    addBlock(x, topY + (2*BLOCK_SIZE), z, 'leaves', dim);
}

function initWorld() {
    console.log("Generating Server World...");
    generateOverworld();
    generateEndWorld();
}

function addBlock(x, y, z, type, dim, state = {}) {
    worldBlocks.set(getKey(x,y,z,dim), { type, state });
}

function spawnMob(type, x, y, z, dim) {
    mobs.push({
        id: Math.random().toString(36).substr(2, 9),
        type: type,
        x: x, y: y, z: z,
        vx: 0, vy: 0, vz: 0,
        dim: dim,
        yaw: 0,
        isDead: false,
        lookAt: {x: 0, y: 0, z: 0},
        health: type === 'villager' ? 5 : (type === 'end_crystal' ? 1 : 3),
        lastAttackTime: 0,
        lastDamageTime: 0,
        aiState: { mode: 'idle', target: null, timer: 0 } // Initialize AI state
    });
}

function checkCactusDamage(entity) {
    const bx = Math.round(entity.x / BLOCK_SIZE) * BLOCK_SIZE;
    const by = Math.round((entity.y - 10) / BLOCK_SIZE) * BLOCK_SIZE;
    const bz = Math.round(entity.z / BLOCK_SIZE) * BLOCK_SIZE;
    
    const nearbyOffsets = [
        {x:0, y:0, z:0}, {x:1, y:0, z:0}, {x:-1, y:0, z:0},
        {x:0, y:0, z:1}, {x:0, y:0, z:-1},
        {x:0, y:1, z:0}, {x:0, y:-1, z:0}
    ];

    for (let o of nearbyOffsets) {
        const k = getKey(bx + o.x*BLOCK_SIZE, by + o.y*BLOCK_SIZE, bz + o.z*BLOCK_SIZE, entity.dim);
        const blockData = worldBlocks.get(k);
        if (blockData && blockData.type === 'cactus') {
            const dist = Math.hypot(entity.x - (bx + o.x*BLOCK_SIZE), entity.z - (bz + o.z*BLOCK_SIZE));
            if (dist < 6) { 
                const now = performance.now();
                if (now - (entity.lastDamageTime || 0) > 500) {
                    entity.health--;
                    if (entity.health <= 0) {
                        entity.isDead = true;
                    }
                    entity.lastDamageTime = now;
                    return true; 
                }
            }
        }
    }
    return false;
}

function createExplosion(x, y, z, dim, radius) {
    const damageRadius = radius * 2.5;
    
    players.forEach(p => {
        if (p.dim !== dim || p.mode === 'creative') return;
        const dist = Math.hypot(p.x - x, p.y - y, p.z - z);
        if (dist < damageRadius) {
            const dmg = Math.floor((1 - dist/damageRadius) * 20);
            if (dmg > 0) {
                p.health -= dmg;
                const client = getClientById(p.id);
                if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                if (p.health <= 0) {
                    p.health = 20;
                    p.x = 0; p.y = 60; p.z = 0;
                    if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                }
            }
        }
    });

    mobs.forEach(m => {
        if (m.dim !== dim || m.isDead || m.type === 'end_crystal') return;
        const dist = Math.hypot(m.x - x, m.y - y, m.z - z);
        if (dist < damageRadius) {
            const dmg = Math.floor((1 - dist/damageRadius) * 20);
            if (dmg > 0) {
                m.health -= dmg;
                if (m.health <= 0) m.isDead = true;
                broadcast({ type: 'entity_update', mob: m });
            }
        }
    });

    const updates = [];
    const r = Math.ceil(radius);
    const centerBx = Math.round(x / BLOCK_SIZE) * BLOCK_SIZE;
    const centerBy = Math.round(y / BLOCK_SIZE) * BLOCK_SIZE;
    const centerBz = Math.round(z / BLOCK_SIZE) * BLOCK_SIZE;

    for (let bx = centerBx - r*BLOCK_SIZE; bx <= centerBx + r*BLOCK_SIZE; bx+=BLOCK_SIZE) {
        for (let by = centerBy - r*BLOCK_SIZE; by <= centerBy + r*BLOCK_SIZE; by+=BLOCK_SIZE) {
            for (let bz = centerBz - r*BLOCK_SIZE; bz <= centerBz + r*BLOCK_SIZE; bz+=BLOCK_SIZE) {
                const dist = Math.hypot(bx - x, by - y, bz - z);
                if (dist <= radius * BLOCK_SIZE) {
                    const k = getKey(bx, by, bz, dim);
                    const blockData = worldBlocks.get(k);
                    if (blockData && !UNBREAKABLE_BLOCKS.includes(blockData.type) && blockData.type !== 'air') {
                        worldBlocks.delete(k); 
                        updates.push({ x: bx, y: by, z: bz, type: 'air', dim: dim });
                    }
                }
            }
        }
    }

    if (updates.length > 0) {
        broadcast({ type: 'world_sync', modifications: updates });
    }
    broadcast({ type: 'explosion', x, y, z, dim });
}

function attemptNaturalMobSpawning() {
    const timeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;
    if (timeRatio < 0.5) return;
    if (mobs.filter(m=>!m.isDead).length > 50) return;

    if (Math.random() < 0.05) {
        const activePlayers = Array.from(players.values()).filter(p => p.dim === 'overworld');
        if (activePlayers.length === 0) return;

        const p = activePlayers[Math.floor(Math.random() * activePlayers.length)];
        
        const angle = Math.random() * Math.PI * 2;
        const dist = 15 * BLOCK_SIZE + Math.random() * 15 * BLOCK_SIZE;
        const sx = p.x + Math.cos(angle) * dist;
        const sz = p.z + Math.sin(angle) * dist;

        let spawnY = -1000;
        const checkX = Math.round(sx / BLOCK_SIZE) * BLOCK_SIZE;
        const checkZ = Math.round(sz / BLOCK_SIZE) * BLOCK_SIZE;

        for(let y=30 * BLOCK_SIZE; y > -10 * BLOCK_SIZE; y-=BLOCK_SIZE) {
             const blockData = worldBlocks.get(getKey(checkX, y, checkZ, 'overworld'));
             if (blockData && blockData.type !== 'air') {
                 spawnY = y + BLOCK_SIZE;
                 break;
             }
        }

        if (spawnY > -900) {
            spawnMob('zombie', checkX, spawnY, checkZ, 'overworld');
            broadcast({ type: 'mob_spawn', x: checkX, y: spawnY, z: checkZ, mobType: 'zombie', dim: 'overworld' });
        }
    }
}

// --- SERVER-SIDE VILLAGER AI ---
function updateVillagerAI(mob, delta, timeRatio) {
    // Only AI for villagers in overworld
    if (mob.type !== 'villager' || mob.dim !== 'overworld') return;

    // Default State
    if (!mob.aiState) mob.aiState = { mode: 'idle', target: null, timer: 0 };
    mob.aiState.timer -= delta;

    const isNight = timeRatio > 0.45 && timeRatio < 0.9;

    // 1. DECISION MAKING
    // If state is mismatched with time, force change
    if (isNight && mob.aiState.mode !== 'sleeping') {
        mob.aiState.mode = 'sleeping';
        // Find nearest house
        if (villagePOIs.length > 0) {
            const houses = villagePOIs.filter(p => p.type === 'house');
            if (houses.length > 0) {
                mob.aiState.target = houses[Math.floor(Math.random() * houses.length)];
            }
        }
    } 
    else if (!isNight && mob.aiState.mode === 'sleeping') {
        // Wake up
        mob.aiState.mode = 'idle';
        mob.aiState.timer = 0; 
    }

    if (!isNight && mob.aiState.timer <= 0) {
        // Day logic switch
        mob.aiState.timer = 5 + Math.random() * 15; // 5-20s duration
        const roll = Math.random();
        if (roll < 0.6) {
            // Farming
            mob.aiState.mode = 'farming';
            const farms = villagePOIs.filter(p => p.type === 'farm');
            if (farms.length > 0) mob.aiState.target = farms[Math.floor(Math.random() * farms.length)];
        } else {
            // Wandering
            mob.aiState.mode = 'wandering';
            // Wander near village center (approx 300, 0 in desert)
            // Random point
            const targetX = 300 * BLOCK_SIZE + (Math.random() - 0.5) * 100; 
            const targetZ = 0 + (Math.random() - 0.5) * 100;
            mob.aiState.target = { x: targetX, z: targetZ };
        }
    }

    // 2. MOVEMENT
    if (mob.aiState.target) {
        const tx = mob.aiState.target.x;
        const tz = mob.aiState.target.z;
        const dx = tx - mob.x;
        const dz = tz - mob.z;
        const dist = Math.sqrt(dx*dx + dz*dz);

        if (dist > 3) { // If not arrived
            const speed = 15;
            mob.vx = (dx / dist) * speed;
            mob.vz = (dz / dist) * speed;
            mob.yaw = Math.atan2(dx, dz); // Look at target

            // Auto Jump Logic check
            // Check block in front
            const lookX = mob.x + (dx/dist) * 3;
            const lookZ = mob.z + (dz/dist) * 3;
            const bx = Math.round(lookX / BLOCK_SIZE) * BLOCK_SIZE;
            const by = Math.round(mob.y / BLOCK_SIZE) * BLOCK_SIZE;
            const bz = Math.round(lookZ / BLOCK_SIZE) * BLOCK_SIZE;
            
            // 1. Cactus Check (Body Level)
            const wallKey = getKey(bx, by, bz, mob.dim);
            const wallBlock = worldBlocks.get(wallKey);
            if (wallBlock && wallBlock.type === 'cactus') {
                mob.vx *= -1; mob.vz *= -1; mob.aiState.timer = 0; return;
            }

            // 2. Void/Cliff Check (Feet Level)
            let hasFloor = false;
            for (let y = by - BLOCK_SIZE; y > -101; y -= BLOCK_SIZE) {
                const floorKey = getKey(bx, y, bz, mob.dim);
                const floorBlock = worldBlocks.get(floorKey);
                if (floorBlock && floorBlock.type !== 'air') {
                    hasFloor = true;
                }
            }
            if (!hasFloor) {
                mob.vx = 0; mob.vz = 0; mob.aiState.timer = 0; return;
            }

            // Auto Jump
            if (wallBlock && wallBlock.type !== 'air' && wallBlock.type !== 'crop' && !wallBlock.type.includes('door')) {
                 // Wall in front, try to jump
                 if (mob.vy === 0) mob.vy = 25;
            }

        } else {
            // Arrived
            mob.vx = 0;
            mob.vz = 0;
            // If farming, maybe spin or look around?
            if (mob.aiState.mode === 'farming') {
                mob.yaw += delta * 2; // Spin slowly looking at crops
            }
        }
    }
}

function updateMobs(delta) {
    const timeRatio = (worldTime % DAY_DURATION) / DAY_DURATION;
    worldTime += delta;
    if (worldTime >= DAY_DURATION) worldTime = 0;

    attemptNaturalMobSpawning();

    players.forEach(p => {
        if (p.mode === 'survival') {
            if (checkCactusDamage(p)) {
                const client = getClientById(p.id);
                if (client) client.send(JSON.stringify({ type: 'damage', health: p.health }));
                if (p.health <= 0) {
                    p.health = 20;
                    p.x=0; p.y=60; p.z=0;
                    if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                }
            }
        }
    });

    mobs.forEach(mob => {
        if (mob.isDead) return;
        if (mob.type === 'end_crystal') return;

        // --- NEW: Update Villager AI ---
        if (mob.type === 'villager') updateVillagerAI(mob, delta, timeRatio);

        if (checkCactusDamage(mob)) {
            if (mob.health <= 0) {
                mob.isDead = true;
                broadcast({ type: 'entity_update', mob: mob });
            } else {
                broadcast({ type: 'entity_update', mob: mob });
            }
        }

        mob.vy -= 9.8 * 50.0 * delta;
        
        let groundY = -101;
        const bx = Math.round(mob.x/5)*5;
        const bz = Math.round(mob.z/5)*5;
        for(let y=Math.floor(mob.y/5)*5; y>-50; y-=5) {
             const kKey = getKey(bx,y,bz,mob.dim);
             const blockData = worldBlocks.get(kKey);
             if(blockData && blockData.type !== 'air' && blockData.type !== 'crop') {
                 groundY = y + 5; 
                 break;
             }
        }

        if (mob.y + mob.vy * delta < groundY) {
            mob.y = groundY;
            mob.vy = 0;
        } else {
            mob.y += mob.vy * delta;
        }

        mob.x += mob.vx * delta;
        mob.z += mob.vz * delta;

        // Zombie AI (Existing)
        let target = null;
        let minDist = 80; 
        let victim = null;
        let isPlayer = false;

        if (mob.type === 'zombie') {
            mobs.forEach(other => {
                if (other.type === 'villager' && !other.isDead && other.dim === mob.dim) {
                    const dist = Math.hypot(mob.x-other.x, mob.y-other.y, mob.z-other.z);
                    if (dist < minDist) {
                        minDist = dist;
                        target = {x: other.x, y: other.y, z: other.z};
                        victim = other;
                        isPlayer = false;
                    }
                }
            });

            players.forEach(p => {
                if (p.mode === 'survival' && p.dim === mob.dim) {
                    const dist = Math.hypot(mob.x-p.x, mob.y-p.y, mob.z-p.z);
                    if (dist < minDist) {
                        minDist = dist;
                        target = {x: p.x, y: p.y, z: p.z};
                        victim = p;
                        isPlayer = true;
                    }
                }
            });

            if (minDist < 8 && target && victim) {
                const now = performance.now();
                if (now - (mob.lastAttackTime || 0) > 1000) {
                    victim.health--;
                    mob.lastAttackTime = now;
                    
                    if (isPlayer) {
                        const client = getClientById(victim.id);
                        if (client) client.send(JSON.stringify({ type: 'damage', health: victim.health }));
                        
                        if (victim.health <= 0) {
                            victim.health = 20;
                            victim.x = 0; victim.y = 60; victim.z = 0; 
                            if (client) client.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                        }
                    } else {
                        if (victim.health <= 0) victim.isDead = true;
                        broadcast({ type: 'entity_update', mob: victim });
                    }
                }
                mob.vx = 0; mob.vz = 0;
            }
        }

        // Apply Zombie Target Movement
        if (target && mob.type === 'zombie') {
            mob.lookAt = {x: target.x, y: mob.y, z: target.z};
            const dx = target.x - mob.x;
            const dz = target.z - mob.z;
            const len = Math.hypot(dx, dz);
            if (len > 0.1) { 
                const speed = 15;
                mob.vx = (dx / len) * speed;
                mob.vz = (dz / len) * speed;
            }
        } else if (mob.type === 'zombie') {
            mob.vx *= 0.9;
            mob.vz *= 0.9;
        }

        if (mob.y < -100) mob.isDead = true;
    });
}

function checkPortalServer(ox, oy, oz, dim) {
    for(let cx=ox-15; cx<=ox+15; cx+=5) for(let cz=oz-15; cz<=oz+15; cz+=5) {
        let complete=true;
        const frames = [
            {x:-1,z:-2},{x:0,z:-2},{x:1,z:-2},
            {x:-1,z:2},{x:0,z:2},{x:1,z:2},
            {x:-2,z:-1},{x:-2,z:0},{x:-2,z:1},
            {x:2,z:-1},{x:2,z:0},{x:2,z:1}
        ];
        
        for(let f of frames) {
            const k = getKey(cx + f.x*5, oy, cz + f.z*5, dim);
            const blockData = worldBlocks.get(k);
            if(!blockData || blockData.type !== 'end_frame_filled') {
                complete = false;
                break;
            }
        }
        
        if(complete) {
            for(let x=-1; x<=1; x++) for(let z=-1; z<=1; z++) {
                const px = cx+x*5, py = oy, pz = cz+z*5;
                addBlock(px, py, pz, 'portal', dim);
                broadcast({ type: 'block_update', x: px, y: py, z: pz, blockType: 'portal', dim: dim, state: {} });
            }
        }
    }
}

function broadcast(msg) {
    const s = JSON.stringify(msg);
    wss.clients.forEach(c => { if(c.readyState === WebSocket.OPEN) c.send(s); });
}

function getClientById(id) {
    for (const client of wss.clients) {
        if (client.playerId === id) return client;
    }
    return null;
}

function assignHost() {
    if (players.size === 0) {
        hostId = null;
        return;
    }
    if (!hostId || !players.has(hostId)) {
        const nextPlayer = players.keys().next().value;
        hostId = nextPlayer;
        const pData = players.get(hostId);
        pData.mode = 'creative'; 
        pData.health = 20; 
        console.log(`New Host Assigned: ${pData.username} (${hostId})`);
        
        const client = getClientById(hostId);
        if (client) client.send(JSON.stringify({ type: 'gamemode', mode: 'creative' }));
    }
}

function getStarterInventory() {
    return {
        'grass': 0, 'dirt': 10, 'stone': 10, 'wood': 10, 
        'leaves': 0, 'sand': 0, 'cactus': 0, 
        'end_frame': 0, 'eye_of_ender': 0, 'network_block': 0
    };
}

wss.on('connection', ws => {
    const id = Math.random().toString(36).substr(2, 9);
    ws.playerId = id;

    let mode = 'survival';
    if (players.size === 0) {
        mode = 'creative';
        hostId = id;
    }

    players.set(id, { 
        id: id, 
        x: 0, y: 60, z: 0, 
        dim: 'overworld', 
        username: 'Guest', 
        mode: mode,
        health: 20,
        maxHealth: 20,
        inventory: getStarterInventory(),
        lastDamageTime: 0
    });

    ws.on('message', msg => {
        try {
            const d = JSON.parse(msg);
            const p = players.get(id);
            
            if(d.type === 'join') {
                p.username = d.username;
                console.log(`${d.username} joined as ${p.mode}`);
                
                ws.send(JSON.stringify({ type: 'gamemode', mode: p.mode }));
                ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));

                for (const [key, blockData] of worldBlocks) {
                    const keySplit = key.split(',');
                    ws.send(JSON.stringify({ 
                        type: "block_update", 
                        x: parseInt(keySplit[0]), 
                        y: parseInt(keySplit[1]), 
                        z: parseInt(keySplit[2]), 
                        blockType: blockData.type,
                        state: blockData.state,
                        dim: keySplit[3] 
                    }));
                }
            }

            if(d.type === 'move') { 
                if(p) { p.x=d.x; p.y=d.y; p.z=d.z; p.yaw=d.yaw; p.dim=d.dim; } 
            }

            if(d.type === 'block_place') {
                if (p.mode === 'survival') {
                    if (p.inventory[d.blockType] && p.inventory[d.blockType] > 0) {
                        p.inventory[d.blockType]--;
                        ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                    } else {
                        return; 
                    }
                }

                addBlock(d.x, d.y, d.z, d.blockType, d.dim, d.state || {});
                broadcast({ type:'block_update', x:d.x, y:d.y, z:d.z, blockType:d.blockType, dim:d.dim, state: d.state || {} });
                if(d.blockType === 'end_frame_filled') checkPortalServer(d.x, d.y, d.z, d.dim);
            }
            
            // New handler for updating state only (toggling doors etc)
            if (d.type === 'block_state_update') {
                const k = getKey(d.x, d.y, d.z, d.dim);
                const existing = worldBlocks.get(k);
                if (existing) {
                    const newState = { ...existing.state, ...d.state };
                    console.log(newState);
                    worldBlocks.set(k, { type: existing.type, state: newState });
                    broadcast({ 
                        type: 'block_update', 
                        x: d.x, y: d.y, z: d.z, 
                        blockType: existing.type, 
                        state: newState, 
                        dim: d.dim 
                    });
                }
            }

            if(d.type === 'block_break') {
                const k = getKey(d.x, d.y, d.z, d.dim);
                const existing = worldBlocks.get(k);
                const existingType = existing ? existing.type : null;
                
                if (existingType && existingType !== 'air') {
                    if (p.mode === 'survival' && UNBREAKABLE_BLOCKS.includes(existingType)) {
                        return;
                    }

                    if (p.mode === 'survival') {
                        let drop = existingType;
                        if (drop === 'end_frame_filled') drop = 'end_frame'; 
                        
                        if (p.inventory[drop] !== undefined) {
                            p.inventory[drop]++;
                            ws.send(JSON.stringify({ type: 'inventory_update', inventory: p.inventory }));
                        }
                    }

                    worldBlocks.delete(k);
                    broadcast({ type:'block_update', x:d.x, y:d.y, z:d.z, blockType:'air', dim:d.dim });
                }
            }

            if (d.type === 'entity_hit') {
                const mob = mobs.find(m => m.id === d.mob);
                if (mob) {
                    if (mob.type === 'end_crystal') {
                        mob.isDead = true;
                        broadcast({ type:'entity_update', mob });
                        createExplosion(mob.x, mob.y, mob.z, mob.dim, 6);
                    } else {
                        mob.health--;
                        if (mob.health <= 0) mob.isDead = true;
                        broadcast({ type:'entity_update', mob });
                    }
                } else {
                    const targetPlayer = players.get(d.mob);
                    if (targetPlayer && targetPlayer.mode === 'survival') {
                        targetPlayer.health--;
                        
                        const victimClient = getClientById(targetPlayer.id);
                        if (victimClient) victimClient.send(JSON.stringify({ type: 'damage', health: targetPlayer.health }));
                        
                        if (targetPlayer.health <= 0) {
                            targetPlayer.health = 20;
                            targetPlayer.x = 0; targetPlayer.y = 60; targetPlayer.z = 0; 
                            if (victimClient) victimClient.send(JSON.stringify({ type: 'respawn', x:0, y:60, z:0 }));
                        }
                    }
                }
            }
        } catch(e) {}
    });
    
    ws.on('close', () => {
        players.delete(id);
        if (id === hostId) {
            console.log("Host left. Migrating...");
            assignHost();
        }
    });
});

initWorld();

setInterval(() => {
    const time = performance.now();
    const delta = (time - prevTime) / 1000;
    if (delta > 1.0) { prevTime = time; return; } 
    
    updateMobs(delta);
    prevTime = time;
    
    broadcast({
        type: 'update',
        players: Array.from(players.values()),
        mobs: mobs.filter(m => !m.isDead),
        timeRatio: worldTime / DAY_DURATION 
    });
}, 50);

console.log("Server running on ws://localhost:8080");