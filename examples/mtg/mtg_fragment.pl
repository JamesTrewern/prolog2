P(X,Y):- Q(X,Z), R(Z,Y) {X,Y,Z}.

%Following rules are extracted from the Comprehensive Rules document effective
%as of August 2018, online here:

%https://media.wizards.com/2018/downloads/MagicCompRules%2020180810.txt

destroy_verb([destroy|T],T).
exile_verb([exile|T],T).
return_verb([return|T],T).

target_permanent(A,B):- target(A,C), permanent_type(C,B).

target([target|T],T).

all_permanents_of_type(A,B):- all(A,C), permanent_types(C,B).

target_artifact_type(A,B):- target(A,C), artifact_type(C,B).
target_creature_type(A,B):- target(A,C), creature_type(C,B).
target_enchantment_type(A,B):- target(A,C), enchantment_type(C,B).
target_land_type(A,B):- target(A,C), land_type(C,B).
target_basic_land_type(A,B):- target(A,C), basic_land_type(C,B).
target_planeswalker_type(A,B):- target(A,C), planeswalker_type(C,B).

all_of_artifact_type(A,B):- all(A,C), artifact_types(C,B).
all_of_creature_type(A,B):- all(A,C), creature_types(C,B).
all_of_enchantment_type(A,B):- all(A,C), enchantment_types(C,B).
all_of_land_type(A,B):- all(A,C), land_types(C,B).
all_of_basic_land_type(A,B):- all(A,C), basic_land_types(C,B).
all_of_planeswalker_type(A,B):- all(A,C), planeswalker_types(C,B).

all([all|T],T).

a_permanent_type([an,artifact|T],T).
a_permanent_type([a,creature|T],T).
a_permanent_type([an,enchantment|T],T).
a_permanent_type([a,land|T],T).
a_permanent_type([a,planeswalker|T],T).

permanent_type([artifact|T],T).
permanent_type([creature|T],T).
permanent_type([enchantment|T],T).
permanent_type([land|T],T).
permanent_type([planeswalker|T],T).

permanent_types([artifacts|T],T).
permanent_types([creatures|T],T).
permanent_types([enchantments|T],T).
permanent_types([lands|T],T).
permanent_types([planeswalkers|T],T).

target_from_battlefield_to_hand(A,B):- target_permanent(A,C), to_owners_hand(C,B).
target_from_graveyard_to_hand(A,B):- target_permanent(A,C),from_graveyard(C,D),to_owners_hand(D,B).
target_from_graveyard_to_battlefield(A,B):- target_permanent(A,C), from_graveyard(C,D), to_battlefield(D,B).

from_battlefield_to_hand(A,B):- a_permanent_type(A,C), to_owners_hand(C,B).
from_graveyard_to_hand(A,B):- a_permanent_type(A,C),from_graveyard(C,D),to_owners_hand(D,B).
from_graveyard_to_battlefield(A,B):- a_permanent_type(A,C), from_graveyard(C,D), to_battlefield(D,B).

all_from_battlefield_to_hand(A,B):- all(A,C),permanents(C,D),to_owners_hands(D,B).
all_from_graveyard_to_hand(A,B):- all(A,C),permanents(C,D), from_graveyard(D,E),to_owners_hands(E,B).
all_from_graveyard_to_battlefield(A,B):- all(A,C),permanents(C,D), from_graveyard(D,E), to_battlefield(E,B).

% See rule 205.3g
artifact_type (['Clue'|T],T).
artifact_type (['Contraption'|T],T).
artifact_type (['Equipment'|T],T).
artifact_type (['Fortification'|T],T).
artifact_type (['Treasure'|T],T).
artifact_type (['Vehicle'|T],T).

% Plural forms by me.
artifact_types (['Clues'|T],T).
artifact_types (['Contraptions'|T],T).
artifact_types (['Equipments'|T],T).
artifact_types (['Fortifications'|T],T).
artifact_types (['Treasures'|T],T).
artifact_types (['Vehicles'|T],T).

% Creature subtypes are shared by tribal spells.
% See rule 205.3m
creature_type (['Advisor'|T],T).
creature_type (['Aetherborn'|T],T).
creature_type (['Ally'|T],T).
creature_type (['Angel'|T],T).
creature_type (['Antelope'|T],T).
creature_type (['Ape'|T],T).
creature_type (['Archer'|T],T).
creature_type (['Archon'|T],T).
creature_type (['Artificer'|T],T).
creature_type (['Assassin'|T],T).
creature_type (['Assembly-Worker'|T],T).
creature_type (['Atog'|T],T).
creature_type (['Aurochs'|T],T).
creature_type (['Avatar'|T],T).
creature_type (['Azra'|T],T).
creature_type (['Badger'|T],T).
creature_type (['Barbarian'|T],T).
creature_type (['Basilisk'|T],T).
creature_type (['Bat'|T],T).
creature_type (['Bear'|T],T).
creature_type (['Beast'|T],T).
creature_type (['Beeble'|T],T).
creature_type (['Berserker'|T],T).
creature_type (['Bird'|T],T).
creature_type (['Blinkmoth'|T],T).
creature_type (['Boar'|T],T).
creature_type (['Bringer'|T],T).
creature_type (['Brushwagg'|T],T).
creature_type (['Camarid'|T],T).
creature_type (['Camel'|T],T).
creature_type (['Caribou'|T],T).
creature_type (['Carrier'|T],T).
creature_type (['Cat'|T],T).
creature_type (['Centaur'|T],T).
creature_type (['Cephalid'|T],T).
creature_type (['Chimera'|T],T).
creature_type (['Citizen'|T],T).
creature_type (['Cleric'|T],T).
creature_type (['Cockatrice'|T],T).
creature_type (['Construct'|T],T).
creature_type (['Coward'|T],T).
creature_type (['Crab'|T],T).
creature_type (['Crocodile'|T],T).
creature_type (['Cyclops'|T],T).
creature_type (['Dauthi'|T],T).
creature_type (['Demon'|T],T).
creature_type (['Deserter'|T],T).
creature_type (['Devil'|T],T).
creature_type (['Dinosaur'|T],T).
creature_type (['Djinn'|T],T).
creature_type (['Dragon'|T],T).
creature_type (['Drake'|T],T).
creature_type (['Dreadnought'|T],T).
creature_type (['Drone'|T],T).
creature_type (['Druid'|T],T).
creature_type (['Dryad'|T],T).
creature_type (['Dwarf'|T],T).
creature_type (['Efreet'|T],T).
creature_type (['Egg'|T],T).
creature_type (['Elder'|T],T).
creature_type (['Eldrazi'|T],T).
creature_type (['Elemental'|T],T).
creature_type (['Elephant'|T],T).
creature_type (['Elf'|T],T).
creature_type (['Elk'|T],T).
creature_type (['Eye'|T],T).
creature_type (['Faerie'|T],T).
creature_type (['Ferret'|T],T).
creature_type (['Fish'|T],T).
creature_type (['Flagbearer'|T],T).
creature_type (['Fox'|T],T).
creature_type (['Frog'|T],T).
creature_type (['Fungus'|T],T).
creature_type (['Gargoyle'|T],T).
creature_type (['Germ'|T],T).
creature_type (['Giant'|T],T).
creature_type (['Gnome'|T],T).
creature_type (['Goat'|T],T).
creature_type (['Goblin'|T],T).
creature_type (['God'|T],T).
creature_type (['Golem'|T],T).
creature_type (['Gorgon'|T],T).
creature_type (['Graveborn'|T],T).
creature_type (['Gremlin'|T],T).
creature_type (['Griffin'|T],T).
creature_type (['Hag'|T],T).
creature_type (['Harpy'|T],T).
creature_type (['Hellion'|T],T).
creature_type (['Hippo'|T],T).
creature_type (['Hippogriff'|T],T).
creature_type (['Homarid'|T],T).
creature_type (['Homunculus'|T],T).
creature_type (['Horror'|T],T).
creature_type (['Horse'|T],T).
creature_type (['Hound'|T],T).
creature_type (['Human'|T],T).
creature_type (['Hydra'|T],T).
creature_type (['Hyena'|T],T).
creature_type (['Illusion'|T],T).
creature_type (['Imp'|T],T).
creature_type (['Incarnation'|T],T).
creature_type (['Insect'|T],T).
creature_type (['Jackal'|T],T).
creature_type (['Jellyfish'|T],T).
creature_type (['Juggernaut'|T],T).
creature_type (['Kavu'|T],T).
creature_type (['Kirin'|T],T).
creature_type (['Kithkin'|T],T).
creature_type (['Knight'|T],T).
creature_type (['Kobold'|T],T).
creature_type (['Kor'|T],T).
creature_type (['Kraken'|T],T).
creature_type (['Lamia'|T],T).
creature_type (['Lammasu'|T],T).
creature_type (['Leech'|T],T).
creature_type (['Leviathan'|T],T).
creature_type (['Lhurgoyf'|T],T).
creature_type (['Licid'|T],T).
creature_type (['Lizard'|T],T).
creature_type (['Manticore'|T],T).
creature_type (['Masticore'|T],T).
creature_type (['Mercenary'|T],T).
creature_type (['Merfolk'|T],T).
creature_type (['Metathran'|T],T).
creature_type (['Minion'|T],T).
creature_type (['Minotaur'|T],T).
creature_type (['Mole'|T],T).
creature_type (['Monger'|T],T).
creature_type (['Mongoose'|T],T).
creature_type (['Monk'|T],T).
creature_type (['Monkey'|T],T).
creature_type (['Moonfolk'|T],T).
creature_type (['Mutant'|T],T).
creature_type (['Myr'|T],T).
creature_type (['Mystic'|T],T).
creature_type (['Naga'|T],T).
creature_type (['Nautilus'|T],T).
creature_type (['Nephilim'|T],T).
creature_type (['Nightmare'|T],T).
creature_type (['Nightstalker'|T],T).
creature_type (['Ninja'|T],T).
creature_type (['Noggle'|T],T).
creature_type (['Nomad'|T],T).
creature_type (['Nymph'|T],T).
creature_type (['Octopus'|T],T).
creature_type (['Ogre'|T],T).
creature_type (['Ooze'|T],T).
creature_type (['Orb'|T],T).
creature_type (['Orc'|T],T).
creature_type (['Orgg'|T],T).
creature_type (['Ouphe'|T],T).
creature_type (['Ox'|T],T).
creature_type (['Oyster'|T],T).
creature_type (['Pangolin'|T],T).
creature_type (['Pegasus'|T],T).
creature_type (['Pentavite'|T],T).
creature_type (['Pest'|T],T).
creature_type (['Phelddagrif'|T],T).
creature_type (['Phoenix'|T],T).
creature_type (['Pilot'|T],T).
creature_type (['Pincher'|T],T).
creature_type (['Pirate'|T],T).
creature_type (['Plant'|T],T).
creature_type (['Praetor'|T],T).
creature_type (['Prism'|T],T).
creature_type (['Processor'|T],T).
creature_type (['Rabbit'|T],T).
creature_type (['Rat'|T],T).
creature_type (['Rebel'|T],T).
creature_type (['Reflection'|T],T).
creature_type (['Rhino'|T],T).
creature_type (['Rigger'|T],T).
creature_type (['Rogue'|T],T).
creature_type (['Sable'|T],T).
creature_type (['Salamander'|T],T).
creature_type (['Samurai'|T],T).
creature_type (['Sand'|T],T).
creature_type (['Saproling'|T],T).
creature_type (['Satyr'|T],T).
creature_type (['Scarecrow'|T],T).
creature_type (['Scion'|T],T).
creature_type (['Scorpion'|T],T).
creature_type (['Scout'|T],T).
creature_type (['Serf'|T],T).
creature_type (['Serpent'|T],T).
creature_type (['Servo'|T],T).
creature_type (['Shade'|T],T).
creature_type (['Shaman'|T],T).
creature_type (['Shapeshifter'|T],T).
creature_type (['Sheep'|T],T).
creature_type (['Siren'|T],T).
creature_type (['Skeleton'|T],T).
creature_type (['Slith'|T],T).
creature_type (['Sliver'|T],T).
creature_type (['Slug'|T],T).
creature_type (['Snake'|T],T).
creature_type (['Soldier'|T],T).
creature_type (['Soltari'|T],T).
creature_type (['Spawn'|T],T).
creature_type (['Specter'|T],T).
creature_type (['Spellshaper'|T],T).
creature_type (['Sphinx'|T],T).
creature_type (['Spider'|T],T).
creature_type (['Spike'|T],T).
creature_type (['Spirit'|T],T).
creature_type (['Splinter'|T],T).
creature_type (['Sponge'|T],T).
creature_type (['Squid'|T],T).
creature_type (['Squirrel'|T],T).
creature_type (['Starfish'|T],T).
creature_type (['Surrakar'|T],T).
creature_type (['Survivor'|T],T).
creature_type (['Tetravite'|T],T).
creature_type (['Thalakos'|T],T).
creature_type (['Thopter'|T],T).
creature_type (['Thrull'|T],T).
creature_type (['Treefolk'|T],T).
creature_type (['Trilobite'|T],T).
creature_type (['Triskelavite'|T],T).
creature_type (['Troll'|T],T).
creature_type (['Turtle'|T],T).
creature_type (['Unicorn'|T],T).
creature_type (['Vampire'|T],T).
creature_type (['Vedalken'|T],T).
creature_type (['Viashino'|T],T).
creature_type (['Volver'|T],T).
creature_type (['Wall'|T],T).
creature_type (['Warrior'|T],T).
creature_type (['Weird'|T],T).
creature_type (['Werewolf'|T],T).
creature_type (['Whale'|T],T).
creature_type (['Wizard'|T],T).
creature_type (['Wolf'|T],T).
creature_type (['Wolverine'|T],T).
creature_type (['Wombat'|T],T).
creature_type (['Worm'|T],T).
creature_type (['Wraith'|T],T).
creature_type (['Wurm'|T],T).
creature_type (['Yeti'|T],T).
creature_type (['Zombie'|T],T).
creature_type (['Zubera'|T],T).

% Don't lose this. Can't always add "s" to end of words to make a plural
% form so after an initial search-and-replace operation this needed
% some hand-editing.
creature_types (['Advisors'|T],T).
creature_types (['Aetherborns'|T],T).
creature_types (['Alles'|T],T).
creature_types (['Angels'|T],T).
creature_types (['Antelopes'|T],T).
creature_types (['Apes'|T],T).
creature_types (['Archers'|T],T).
creature_types (['Archons'|T],T).
creature_types (['Artificers'|T],T).
creature_types (['Assassins'|T],T).
creature_types (['Assembly-Workers'|T],T).
creature_types (['Atogs'|T],T).
creature_types (['Aurochs'|T],T).
creature_types (['Avatars'|T],T).
creature_types (['Azras'|T],T).
creature_types (['Badgers'|T],T).
creature_types (['Barbarians'|T],T).
creature_types (['Basilisks'|T],T).
creature_types (['Bats'|T],T).
creature_types (['Bears'|T],T).
creature_types (['Beasts'|T],T).
creature_types (['Beebles'|T],T).
creature_types (['Berserkers'|T],T).
creature_types (['Birds'|T],T).
creature_types (['Blinkmoths'|T],T).
creature_types (['Boars'|T],T).
creature_types (['Bringers'|T],T).
creature_types (['Brushwaggs'|T],T).
creature_types (['Camarids'|T],T).
creature_types (['Camels'|T],T).
creature_types (['Caribou'|T],T).
creature_types (['Carriers'|T],T).
creature_types (['Cats'|T],T).
creature_types (['Centaurs'|T],T).
creature_types (['Cephalids'|T],T).
creature_types (['Chimeras'|T],T).
creature_types (['Citizens'|T],T).
creature_types (['Clerics'|T],T).
creature_types (['Cockatrices'|T],T).
creature_types (['Constructs'|T],T).
creature_types (['Cowards'|T],T).
creature_types (['Crabs'|T],T).
creature_types (['Crocodiles'|T],T).
creature_types (['Cyclopss'|T],T).
creature_types (['Dauthis'|T],T).
creature_types (['Demons'|T],T).
creature_types (['Deserters'|T],T).
creature_types (['Devils'|T],T).
creature_types (['Dinosaurs'|T],T).
creature_types (['Djinns'|T],T).
creature_types (['Dragons'|T],T).
creature_types (['Drakes'|T],T).
creature_types (['Dreadnoughts'|T],T).
creature_types (['Drones'|T],T).
creature_types (['Druids'|T],T).
creature_types (['Dryads'|T],T).
creature_types (['Dwarfs'|T],T).
creature_types (['Efreets'|T],T).
creature_types (['Eggs'|T],T).
creature_types (['Elders'|T],T).
creature_types (['Eldrazis'|T],T).
creature_types (['Elementals'|T],T).
creature_types (['Elephants'|T],T).
creature_types (['Elves'|T],T).
creature_types (['Elks'|T],T).
creature_types (['Eyes'|T],T).
creature_types (['Faeries'|T],T).
creature_types (['Ferrets'|T],T).
creature_types (['Fish'|T],T).
creature_types (['Flagbearers'|T],T).
creature_types (['Foxes'|T],T).
creature_types (['Frogs'|T],T).
creature_types (['Fungi'|T],T).
creature_types (['Gargoyles'|T],T).
creature_types (['Germs'|T],T).
creature_types (['Giants'|T],T).
creature_types (['Gnomes'|T],T).
creature_types (['Goats'|T],T).
creature_types (['Goblins'|T],T).
creature_types (['Gods'|T],T).
creature_types (['Golems'|T],T).
creature_types (['Gorgons'|T],T).
creature_types (['Graveborns'|T],T).
creature_types (['Gremlins'|T],T).
creature_types (['Griffins'|T],T).
creature_types (['Hags'|T],T).
creature_types (['Harpies'|T],T).
creature_types (['Hellions'|T],T).
creature_types (['Hippos'|T],T).
creature_types (['Hippogriffs'|T],T).
creature_types (['Homarids'|T],T).
creature_types (['Homunculuss'|T],T).
creature_types (['Horrors'|T],T).
creature_types (['Horses'|T],T).
creature_types (['Hounds'|T],T).
creature_types (['Humans'|T],T).
creature_types (['Hydras'|T],T).
creature_types (['Hyenas'|T],T).
creature_types (['Illusions'|T],T).
creature_types (['Imps'|T],T).
creature_types (['Incarnations'|T],T).
creature_types (['Insects'|T],T).
creature_types (['Jackals'|T],T).
creature_types (['Jellyfishs'|T],T).
creature_types (['Juggernauts'|T],T).
creature_types (['Kavu'|T],T).
creature_types (['Kirins'|T],T).
creature_types (['Kithkins'|T],T).
creature_types (['Knights'|T],T).
creature_types (['Kobolds'|T],T).
creature_types (['Kors'|T],T).
creature_types (['Krakens'|T],T).
creature_types (['Lamias'|T],T).
creature_types (['Lammasu'|T],T).
creature_types (['Leeches'|T],T).
creature_types (['Leviathans'|T],T).
creature_types (['Lhurgoyfs'|T],T).
creature_types (['Licids'|T],T).
creature_types (['Lizards'|T],T).
creature_types (['Manticores'|T],T).
creature_types (['Masticores'|T],T).
creature_types (['Mercenaries'|T],T).
creature_types (['Merfolks'|T],T).
creature_types (['Metathran'|T],T).
creature_types (['Minions'|T],T).
creature_types (['Minotaurs'|T],T).
creature_types (['Moles'|T],T).
creature_types (['Mongers'|T],T).
creature_types (['Mongeese'|T],T).
creature_types (['Monks'|T],T).
creature_types (['Monkeys'|T],T).
creature_types (['Moonfolks'|T],T).
creature_types (['Mutants'|T],T).
creature_types (['Myr'|T],T).
creature_types (['Mystics'|T],T).
creature_types (['Naga'|T],T).
creature_types (['Nautili'|T],T).
creature_types (['Nephilim'|T],T).
creature_types (['Nightmares'|T],T).
creature_types (['Nightstalkers'|T],T).
creature_types (['Ninjas'|T],T).
creature_types (['Noggles'|T],T).
creature_types (['Nomads'|T],T).
creature_types (['Nymphs'|T],T).
creature_types (['Octopi'|T],T).
creature_types (['Ogres'|T],T).
creature_types (['Oozes'|T],T).
creature_types (['Orbs'|T],T).
creature_types (['Orcs'|T],T).
creature_types (['Orggs'|T],T).
creature_types (['Ouphes'|T],T).
creature_types (['Oxen'|T],T).
creature_types (['Oysters'|T],T).
creature_types (['Pangolins'|T],T).
creature_types (['Pegasi'|T],T).
creature_types (['Pentavites'|T],T).
creature_types (['Pests'|T],T).
creature_types (['Phelddagrifs'|T],T).
creature_types (['Phoenixes'|T],T).
creature_types (['Pilots'|T],T).
creature_types (['Pinchers'|T],T).
creature_types (['Pirates'|T],T).
creature_types (['Plants'|T],T).
creature_types (['Praetors'|T],T).
creature_types (['Prisms'|T],T).
creature_types (['Processors'|T],T).
creature_types (['Rabbits'|T],T).
creature_types (['Rats'|T],T).
creature_types (['Rebels'|T],T).
creature_types (['Reflections'|T],T).
creature_types (['Rhinos'|T],T).
creature_types (['Riggers'|T],T).
creature_types (['Rogues'|T],T).
creature_types (['Sables'|T],T).
creature_types (['Salamanders'|T],T).
creature_types (['Samurais'|T],T).
creature_types (['Sands'|T],T).
creature_types (['Saprolings'|T],T).
creature_types (['Satyrs'|T],T).
creature_types (['Scarecrows'|T],T).
creature_types (['Scions'|T],T).
creature_types (['Scorpions'|T],T).
creature_types (['Scouts'|T],T).
creature_types (['Serfs'|T],T).
creature_types (['Serpents'|T],T).
creature_types (['Servos'|T],T).
creature_types (['Shades'|T],T).
creature_types (['Shamans'|T],T).
creature_types (['Shapeshifters'|T],T).
creature_types (['Sheeps'|T],T).
creature_types (['Sirens'|T],T).
creature_types (['Skeletons'|T],T).
creature_types (['Sliths'|T],T).
creature_types (['Slivers'|T],T).
creature_types (['Slugs'|T],T).
creature_types (['Snakes'|T],T).
creature_types (['Soldiers'|T],T).
creature_types (['Soltaris'|T],T).
creature_types (['Spawns'|T],T).
creature_types (['Specters'|T],T).
creature_types (['Spellshapers'|T],T).
creature_types (['Sphinxes'|T],T).
creature_types (['Spiders'|T],T).
creature_types (['Spikes'|T],T).
creature_types (['Spirits'|T],T).
creature_types (['Splinters'|T],T).
creature_types (['Sponges'|T],T).
creature_types (['Squids'|T],T).
creature_types (['Squirrels'|T],T).
creature_types (['Starfish'|T],T).
creature_types (['Surrakars'|T],T).
creature_types (['Survivors'|T],T).
creature_types (['Tetravites'|T],T).
creature_types (['Thalakoi'|T],T).
creature_types (['Thopters'|T],T).
creature_types (['Thrulls'|T],T).
creature_types (['Treefolks'|T],T).
creature_types (['Trilobites'|T],T).
creature_types (['Triskelavites'|T],T).
creature_types (['Trolls'|T],T).
creature_types (['Turtles'|T],T).
creature_types (['Unicorns'|T],T).
creature_types (['Vampires'|T],T).
creature_types (['Vedalkens'|T],T).
creature_types (['Viashinos'|T],T).
creature_types (['Volvers'|T],T).
creature_types (['Walls'|T],T).
creature_types (['Warriors'|T],T).
creature_types (['Weirds'|T],T).
creature_types (['Werewolves'|T],T).
creature_types (['Whales'|T],T).
creature_types (['Wizards'|T],T).
creature_types (['Wolves'|T],T).
creature_types (['Wolverines'|T],T).
creature_types (['Wombats'|T],T).
creature_types (['Worms'|T],T).
creature_types (['Wraiths'|T],T).
creature_types (['Wurms'|T],T).
creature_types (['Yetis'|T],T).
creature_types (['Zombies'|T],T).
creature_types (['Zuberas'|T],T).

% See rule 205.3h
enchantment_type (['Aura'|T],T).
enchantment_type (['Cartouche'|T],T).
enchantment_type (['Curse'|T],T).
enchantment_type (['Saga'|T],T).
enchantment_type (['Shrine'|T],T).

% My plurals.
enchantment_types (['Auras'|T],T).
enchantment_types (['Cartouches'|T],T).
enchantment_types (['Curses'|T],T).
enchantment_types (['Sagas'|T],T).
enchantment_types (['Shrines'|T],T).

% See rule 205.3i
land_type (['Desert'|T],T).
land_type (['Forest'|T],T).
land_type (['Gate'|T],T).
land_type (['Island'|T],T).
land_type (['Lair'|T],T).
land_type (['Locus'|T],T).
land_type (['Mine'|T],T).
land_type (['Mountain'|T],T).
land_type (['Plains'|T],T).
land_type (['Power-Plant'|T],T).
land_type (['Swamp'|T],T).
land_type (['Tower'|T],T).
land_type (['Urzas'|T],T).

% My plurals
land_types (['Deserts'|T],T).
land_types (['Forests'|T],T).
land_types (['Gates'|T],T).
land_types (['Islands'|T],T).
land_types (['Lairs'|T],T).
land_types (['Loci'|T],T).
land_types (['Mines'|T],T).
land_types (['Mountains'|T],T).
land_types (['Plains'|T],T).
land_types (['Power-Plants'|T],T).
land_types (['Swamps'|T],T).
land_types (['Towers'|T],T).
land_types (['Urzas'|T],T).

% See rule 205.3i
basic_land_type (['Forest'|T],T).
basic_land_type (['Island'|T],T).
basic_land_type (['Mountain'|T],T).
basic_land_type (['Plains'|T],T).
basic_land_type (['Swamp'|T],T).

% My plurals
basic_land_types (['Forest'|T],T).
basic_land_types (['Island'|T],T).
basic_land_types (['Mountain'|T],T).
basic_land_types (['Plains'|T],T).
basic_land_types (['Swamp'|T],T).

% See rule 205.3j
planeswalker_type (['Ajani'|T],T).
planeswalker_type (['Aminatou'|T],T).
planeswalker_type (['Angrath'|T],T).
planeswalker_type (['Arlinn'|T],T).
planeswalker_type (['Ashiok'|T],T).
planeswalker_type (['Bolas'|T],T).
planeswalker_type (['Chandra'|T],T).
planeswalker_type (['Dack'|T],T).
planeswalker_type (['Daretti'|T],T).
planeswalker_type (['Domri'|T],T).
planeswalker_type (['Dovin'|T],T).
planeswalker_type (['Elspeth'|T],T).
planeswalker_type (['Estrid'|T],T).
planeswalker_type (['Freyalise'|T],T).
planeswalker_type (['Garruk'|T],T).
planeswalker_type (['Gideon'|T],T).
planeswalker_type (['Huatli'|T],T).
planeswalker_type (['Jace'|T],T).
planeswalker_type (['Jaya'|T],T).
planeswalker_type (['Karn'|T],T).
planeswalker_type (['Kaya'|T],T).
planeswalker_type (['Kiora'|T],T).
planeswalker_type (['Koth'|T],T).
planeswalker_type (['Liliana'|T],T).
planeswalker_type (['Nahiri'|T],T).
planeswalker_type (['Narset'|T],T).
planeswalker_type (['Nissa'|T],T).
planeswalker_type (['Nixilis'|T],T).
planeswalker_type (['Ral'|T],T).
planeswalker_type (['Rowan'|T],T).
planeswalker_type (['Saheeli'|T],T).
planeswalker_type (['Samut'|T],T).
planeswalker_type (['Sarkhan'|T],T).
planeswalker_type (['Sorin'|T],T).
planeswalker_type (['Tamiyo'|T],T).
planeswalker_type (['Teferi'|T],T).
planeswalker_type (['Tezzeret'|T],T).
planeswalker_type (['Tibalt'|T],T).
planeswalker_type (['Ugin'|T],T).
planeswalker_type (['Venser'|T],T).
planeswalker_type (['Vivien'|T],T).
planeswalker_type (['Vraska'|T],T).
planeswalker_type (['Will'|T],T).
planeswalker_type (['Windgrace'|T],T).
planeswalker_type (['Xenagos'|T],T).
planeswalker_type (['Yanggu'|T],T).
planeswalker_type (['Yanling'|T],T).

% No idea whether these can be made plural
planeswalker_types (['Ajani'|T],T).
planeswalker_types (['Aminatou'|T],T).
planeswalker_types (['Angrath'|T],T).
planeswalker_types (['Arlinn'|T],T).
planeswalker_types (['Ashiok'|T],T).
planeswalker_types (['Bolas'|T],T).
planeswalker_types (['Chandra'|T],T).
planeswalker_types (['Dack'|T],T).
planeswalker_types (['Daretti'|T],T).
planeswalker_types (['Domri'|T],T).
planeswalker_types (['Dovin'|T],T).
planeswalker_types (['Elspeth'|T],T).
planeswalker_types (['Estrid'|T],T).
planeswalker_types (['Freyalise'|T],T).
planeswalker_types (['Garruk'|T],T).
planeswalker_types (['Gideon'|T],T).
planeswalker_types (['Huatli'|T],T).
planeswalker_types (['Jace'|T],T).
planeswalker_types (['Jaya'|T],T).
planeswalker_types (['Karn'|T],T).
planeswalker_types (['Kaya'|T],T).
planeswalker_types (['Kiora'|T],T).
planeswalker_types (['Koth'|T],T).
planeswalker_types (['Liliana'|T],T).
planeswalker_types (['Nahiri'|T],T).
planeswalker_types (['Narset'|T],T).
planeswalker_types (['Nissa'|T],T).
planeswalker_types (['Nixilis'|T],T).
planeswalker_types (['Ral'|T],T).
planeswalker_types (['Rowan'|T],T).
planeswalker_types (['Saheeli'|T],T).
planeswalker_types (['Samut'|T],T).
planeswalker_types (['Sarkhan'|T],T).
planeswalker_types (['Sorin'|T],T).
planeswalker_types (['Tamiyo'|T],T).
planeswalker_types (['Teferi'|T],T).
planeswalker_types (['Tezzeret'|T],T).
planeswalker_types (['Tibalt'|T],T).
planeswalker_types (['Ugin'|T],T).
planeswalker_types (['Venser'|T],T).
planeswalker_types (['Vivien'|T],T).
planeswalker_types (['Vraska'|T],T).
planeswalker_types (['Will'|T],T).
planeswalker_types (['Windgrace'|T],T).
planeswalker_types (['Xenagos'|T],T).
planeswalker_types (['Yanggu'|T],T).
planeswalker_types (['Yanling'|T],T).